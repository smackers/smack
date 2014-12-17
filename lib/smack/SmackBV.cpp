//
// This file is distributed under the MIT License. See LICENSE for details.
//
//#define DEBUG_TYPE "smack-mod-gen"
#include "smack/SmackBV.h"
#include "llvm/IR/InstIterator.h"

namespace smack {

llvm::RegisterPass<SmackBV> BV("smack-bv", "SMACK bit-vector checker");
char SmackBV::ID = 0;
bool SmackBV::misBVRequired = false;

bool SmackBV::isBVPredicate(unsigned opcode)
{
	return ((opcode >= llvm::Instruction::And) && (opcode <= llvm::Instruction::Xor));
}

bool SmackBV::isBVRequired()
{
	return misBVRequired;
}

bool SmackBV::runOnModule(llvm::Module &m) 
{
	for (llvm::Module::iterator func = m.begin(), fe = m.end(); func != fe; ++func) {
		for (llvm::inst_iterator inst = inst_begin(func), inste = inst_end(func); inst != inste; ++inst) {
			if (inst->isShift() || isBVPredicate(inst->getOpcode())) {
				misBVRequired = true;
				return false;
			}
		}
	}	
	return false;
}
} // namespace smack

