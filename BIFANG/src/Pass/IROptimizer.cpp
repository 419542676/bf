#include <queue>
#include "Pass/IROptimizer.h"
#include "Pass/DomTreePass.h"
#include "Pass/LiveVariableAnalysis.h"
#include "Pass/Mem2RegPass.h"
#include "Pass/OptUtils.h"

IROptimizer::IROptimizer(GlobalUnit *gu) {
    this->globalUnit = gu;
}

void IROptimizer::Optimize() {
    // Dom Tree & DF

    BuildCFG();
    Constlize();
    ScalarOpt();

    //globalUnit->Emit(std::cerr);
    DomTreePass* domTreePass = new DomTreePass(this->globalUnit);
    domTreePass->run();

    //LVA
    LiveVariableAnalysis* lva = new LiveVariableAnalysis(this->globalUnit);
    lva->analysis();

    //Mem2reg
    Mem2RegPass* mem2reg = new Mem2RegPass(this->globalUnit);
    mem2reg->run();

}

void IROptimizer::BuildCFG() {
    // 1.bfs && remove unvisited blocks
    for(auto&[name,func]: globalUnit->func_table){
        if(func->entry == nullptr) continue;

        set<BasicBlock*> vis;
        queue<BasicBlock*> q;
        q.push(func->entry);
        while(!q.empty()){
            BasicBlock * block = q.front(); q.pop();
            if(vis.count(block)) continue;
            vis.insert(block);
            for(auto bb:block->succ){
                q.push(bb);
            }
        }

        auto& v = func->block_list;
        vector<BasicBlock *> not_visited;
        for(auto & it : v){
            if(!vis.count(it)){ // not visited
                not_visited.push_back(it);
            }
        }

        for(auto bb:not_visited){
            DelBlock(bb);
        }
    }
}

void IROptimizer::debug() {
    for(auto&[name,func]:globalUnit->func_table){
        for(auto block: func->block_list){
            for(auto instr: block->local_instr){
                if(!instr->def_list.empty()){
                    ValueRef * def = *(instr->def_list.begin());
                    cerr << def->name << " :" << endl;
                    for(auto use : def->use){
                        use->outPut(std::cerr);
                    }
                }
            }
        }
    }
}

void IROptimizer::Constlize() {
    for(auto &[name,symbol]: globalUnit->global_symbol_table){
        if(symbol->symbolType->type != ARRAYTYPE && symbol->def.empty()){
            for(auto load: symbol->use){
                ValueRef* val = *(load->def_list.begin());
                replaceAllUsesOf(val,symbol->constVal);
            }
        }
    }
}

namespace {
bool IsIntConst(ValueRef *ref) {
    return ref && ref->type == IntConst;
}

bool IsBoolConst(ValueRef *ref) {
    return ref && ref->type == BoolConst;
}

int GetIntConst(ValueRef *ref) {
    return static_cast<Int_Const*>(ref)->value;
}

bool GetBoolConst(ValueRef *ref) {
    return static_cast<Bool_Const*>(ref)->value;
}

ValueRef *MakeIntConst(int value) {
    return new Int_Const(value);
}

ValueRef *MakeBoolConst(bool value) {
    return new Bool_Const(value);
}

bool IsConstValue(ValueRef *ref) {
    return IsIntConst(ref) || IsBoolConst(ref);
}

bool GetConstAsBool(ValueRef *ref) {
    if (IsBoolConst(ref)) {
        return GetBoolConst(ref);
    }
    return GetIntConst(ref) != 0;
}

ValueRef *FoldBinary(BinaryInstruction *instr) {
    if (!IsIntConst(instr->src1) || !IsIntConst(instr->src2)) {
        return nullptr;
    }
    int lhs = GetIntConst(instr->src1);
    int rhs = GetIntConst(instr->src2);
    switch (instr->opTy) {
        case ADD: return MakeIntConst(lhs + rhs);
        case SUB: return MakeIntConst(lhs - rhs);
        case MUL: return MakeIntConst(lhs * rhs);
        case DIV:
            if (rhs == 0) return nullptr;
            return MakeIntConst(lhs / rhs);
        case MOD:
            if (rhs == 0) return nullptr;
            return MakeIntConst(lhs % rhs);
        case AND: return MakeIntConst(lhs & rhs);
        case OR: return MakeIntConst(lhs | rhs);
        default: return nullptr;
    }
}

ValueRef *FoldCmp(CmpInstruction *instr) {
    if (!IsConstValue(instr->src1) || !IsConstValue(instr->src2)) {
        return nullptr;
    }
    int lhs = IsBoolConst(instr->src1) ? static_cast<int>(GetBoolConst(instr->src1)) : GetIntConst(instr->src1);
    int rhs = IsBoolConst(instr->src2) ? static_cast<int>(GetBoolConst(instr->src2)) : GetIntConst(instr->src2);
    bool result = false;
    switch (instr->opTy) {
        case EQ: result = lhs == rhs; break;
        case NE: result = lhs != rhs; break;
        case LT: result = lhs < rhs; break;
        case LE: result = lhs <= rhs; break;
        case GT: result = lhs > rhs; break;
        case GE: result = lhs >= rhs; break;
        default: return nullptr;
    }
    return MakeBoolConst(result);
}

ValueRef *FoldZExt(ZExtInstruction *instr) {
    if (!IsBoolConst(instr->src)) {
        return nullptr;
    }
    return MakeIntConst(GetBoolConst(instr->src) ? 1 : 0);
}

ValueRef *FoldXor(XorInstruction *instr) {
    if (!IsBoolConst(instr->src)) {
        return nullptr;
    }
    return MakeBoolConst(!GetBoolConst(instr->src));
}

ValueRef *FoldFNeg(FNegInstruction *instr) {
    if (!instr->src || instr->src->type != FloatConst) {
        return nullptr;
    }
    auto value = static_cast<Float_Const*>(instr->src)->value;
    return new Float_Const(-value);
}

ValueRef *FoldSll(SllInstruction *instr) {
    if (!IsIntConst(instr->src1) || !IsIntConst(instr->bits)) {
        return nullptr;
    }
    int bits = GetIntConst(instr->bits) & 31;
    return MakeIntConst(GetIntConst(instr->src1) << bits);
}

ValueRef *FoldSra(SraInstruction *instr) {
    if (!IsIntConst(instr->src1) || !IsIntConst(instr->bits)) {
        return nullptr;
    }
    int bits = GetIntConst(instr->bits) & 31;
    return MakeIntConst(GetIntConst(instr->src1) >> bits);
}

void ReplaceWithConst(Instruction *instr, ValueRef *replacement) {
    if (instr->def_list.empty()) {
        return;
    }
    ValueRef *def = *(instr->def_list.begin());
    replaceAllUsesOf(def, replacement);
    DeleteInstruction(instr);
}

bool SimplifyBinary(BinaryInstruction *instr) {
    if (IsIntConst(instr->src1) && IsIntConst(instr->src2)) {
        ValueRef *folded = FoldBinary(instr);
        if (!folded) {
            return false;
        }
        ReplaceWithConst(instr, folded);
        return true;
    }
    if (instr->opTy == ADD) {
        if (IsIntConst(instr->src1) && GetIntConst(instr->src1) == 0) {
            replaceAllUsesOf(instr->dst, instr->src2);
            DeleteInstruction(instr);
            return true;
        }
        if (IsIntConst(instr->src2) && GetIntConst(instr->src2) == 0) {
            replaceAllUsesOf(instr->dst, instr->src1);
            DeleteInstruction(instr);
            return true;
        }
    } else if (instr->opTy == SUB) {
        if (IsIntConst(instr->src2) && GetIntConst(instr->src2) == 0) {
            replaceAllUsesOf(instr->dst, instr->src1);
            DeleteInstruction(instr);
            return true;
        }
    } else if (instr->opTy == MUL) {
        if (IsIntConst(instr->src1)) {
            int lhs = GetIntConst(instr->src1);
            if (lhs == 0) {
                ReplaceWithConst(instr, MakeIntConst(0));
                return true;
            }
            if (lhs == 1) {
                replaceAllUsesOf(instr->dst, instr->src2);
                DeleteInstruction(instr);
                return true;
            }
        }
        if (IsIntConst(instr->src2)) {
            int rhs = GetIntConst(instr->src2);
            if (rhs == 0) {
                ReplaceWithConst(instr, MakeIntConst(0));
                return true;
            }
            if (rhs == 1) {
                replaceAllUsesOf(instr->dst, instr->src1);
                DeleteInstruction(instr);
                return true;
            }
        }
    } else if (instr->opTy == AND) {
        if (IsIntConst(instr->src1) && GetIntConst(instr->src1) == 0) {
            ReplaceWithConst(instr, MakeIntConst(0));
            return true;
        }
        if (IsIntConst(instr->src2) && GetIntConst(instr->src2) == 0) {
            ReplaceWithConst(instr, MakeIntConst(0));
            return true;
        }
    } else if (instr->opTy == OR) {
        if (IsIntConst(instr->src1) && GetIntConst(instr->src1) == 0) {
            replaceAllUsesOf(instr->dst, instr->src2);
            DeleteInstruction(instr);
            return true;
        }
        if (IsIntConst(instr->src2) && GetIntConst(instr->src2) == 0) {
            replaceAllUsesOf(instr->dst, instr->src1);
            DeleteInstruction(instr);
            return true;
        }
    }
    return false;
}

bool SimplifyCmp(CmpInstruction *instr) {
    ValueRef *folded = FoldCmp(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifyZExt(ZExtInstruction *instr) {
    ValueRef *folded = FoldZExt(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifyXor(XorInstruction *instr) {
    ValueRef *folded = FoldXor(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifyFNeg(FNegInstruction *instr) {
    ValueRef *folded = FoldFNeg(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifySll(SllInstruction *instr) {
    ValueRef *folded = FoldSll(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifySra(SraInstruction *instr) {
    ValueRef *folded = FoldSra(instr);
    if (!folded) {
        return false;
    }
    ReplaceWithConst(instr, folded);
    return true;
}

bool SimplifyCondBr(CondBrInstruction *instr) {
    if (!IsConstValue(instr->condition)) {
        return false;
    }
    bool taken = GetConstAsBool(instr->condition);
    BasicBlock *target = taken ? instr->trueLabel : instr->falseLabel;
    BasicBlock *drop = taken ? instr->falseLabel : instr->trueLabel;
    UnlinkBlock(instr->block, drop);
    auto br = new BrInstruction(target);
    br->block = instr->block;
    ReplaceInstr(instr, br);
    return true;
}
} // namespace

void IROptimizer::ScalarOpt() {
    for (auto &[name, func] : globalUnit->func_table) {
        if (func->entry == nullptr) {
            continue;
        }
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto block : func->block_list) {
                auto &instrs = block->local_instr;
                for (auto it = instrs.begin(); it != instrs.end();) {
                    Instruction *instr = *it;
                    if (instr->deleted) {
                        it = instrs.erase(it);
                        continue;
                    }
                    bool folded = false;
                    switch (instr->instType) {
                        case BINARY:
                            folded = SimplifyBinary(dynamic_cast<BinaryInstruction*>(instr));
                            break;
                        case CMP:
                            folded = SimplifyCmp(dynamic_cast<CmpInstruction*>(instr));
                            break;
                        case ZEXT:
                            folded = SimplifyZExt(dynamic_cast<ZExtInstruction*>(instr));
                            break;
                        case XOR:
                            folded = SimplifyXor(dynamic_cast<XorInstruction*>(instr));
                            break;
                        case FNEG:
                            folded = SimplifyFNeg(dynamic_cast<FNegInstruction*>(instr));
                            break;
                        case SLL:
                            folded = SimplifySll(dynamic_cast<SllInstruction*>(instr));
                            break;
                        case SRA:
                            folded = SimplifySra(dynamic_cast<SraInstruction*>(instr));
                            break;
                        case CONDBR:
                            folded = SimplifyCondBr(dynamic_cast<CondBrInstruction*>(instr));
                            break;
                        default:
                            break;
                    }
                    if (folded) {
                        changed = true;
                        it = instrs.begin();
                        continue;
                    }
                    ++it;
                }
            }
        }
    }
}
