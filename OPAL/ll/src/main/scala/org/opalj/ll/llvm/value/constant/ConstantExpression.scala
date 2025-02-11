/* BSD 2-Clause License - see OPAL/LICENSE for details. */
package org.opalj.ll.llvm.value
package constant

import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM._
import org.opalj.ll.llvm.value.User

object ConstantExpression {
    def apply(ref: LLVMValueRef): ConstantExpression = {
        assert(ref != null && !ref.isNull(), "ref may not be null")
        assert(LLVMGetValueKind(ref) == LLVMConstantExprValueKind, "ref has to be an instruction")
        LLVMGetConstOpcode(ref) match {
            // case LLVMRet            => RetConst(ref)
            // case LLVMBr             => BrConst(ref)
            // case LLVMSwitch         => SwitchConst(ref)
            // case LLVMIndirectBr     => IndirectBrConst(ref)
            // case LLVMInvoke         => InvokeConst(ref)
            // case LLVMUnreachable    => UnreachableConst(ref)
            // case LLVMCallBr         => CallBrConst(ref)
            // case LLVMFNeg           => FNegConst(ref)
            // case LLVMAdd            => AddConst(ref)
            // case LLVMFAdd           => FAddConst(ref)
            // case LLVMSub            => SubConst(ref)
            // case LLVMFSub           => FSubConst(ref)
            // case LLVMMul            => MulConst(ref)
            // case LLVMFMul           => FMulConst(ref)
            // case LLVMUDiv           => UDivConst(ref)
            // case LLVMSDiv           => SDivConst(ref)
            // case LLVMFDiv           => FDivConst(ref)
            // case LLVMURem           => URemConst(ref)
            // case LLVMSRem           => SRemConst(ref)
            // case LLVMFRem           => FRemConst(ref)
            // case LLVMShl            => ShlConst(ref)
            // case LLVMLShr           => LShrConst(ref)
            // case LLVMAShr           => AShrConst(ref)
            // case LLVMAnd            => AndConst(ref)
            // case LLVMOr             => OrConst(ref)
            // case LLVMXor            => XorConst(ref)
            // case LLVMAlloca         => AllocaConst(ref)
            // case LLVMLoad           => LoadConst(ref)
            // case LLVMStore          => StoreConst(ref)
            case LLVMGetElementPtr => GetElementPtrConst(ref)
            // case LLVMTrunc          => TruncConst(ref)
            // case LLVMZExt           => ZExtConst(ref)
            // case LLVMSExt           => SExtConst(ref)
            // case LLVMFPToUI         => FPToUIConst(ref)
            // case LLVMFPToSI         => FPToSIConst(ref)
            // case LLVMUIToFP         => UIToFPConst(ref)
            // case LLVMSIToFP         => SIToFPConst(ref)
            // case LLVMFPTrunc        => FPTruncConst(ref)
            // case LLVMFPExt          => FPExtConst(ref)
            // case LLVMPtrToInt       => PtrToIntConst(ref)
            // case LLVMIntToPtr       => IntToPtrConst(ref)
            // case LLVMBitCast        => BitCastConst(ref)
            // case LLVMAddrSpaceCast  => AddrSpaceCastConst(ref)
            // case LLVMICmp           => ICmpConst(ref)
            // case LLVMFCmp           => FCmpConst(ref)
            // case LLVMPHI            => PHIConst(ref)
            // case LLVMCall           => CallConst(ref)
            // case LLVMSelect         => SelectConst(ref)
            // case LLVMUserOp1        => UserOp1Const(ref)
            // case LLVMUserOp2        => UserOp2Const(ref)
            // case LLVMVAArg          => VAArgConst(ref)
            // case LLVMExtractElement => ExtractElementConst(ref)
            // case LLVMInsertElement  => InsertElementConst(ref)
            // case LLVMShuffleVector  => ShuffleVectorConst(ref)
            // case LLVMExtractValue   => ExtractValueConst(ref)
            // case LLVMInsertValue    => InsertValueConst(ref)
            // case LLVMFreeze         => FreezeConst(ref)
            // case LLVMFence          => FenceConst(ref)
            // case LLVMAtomicCmpXchg  => AtomicCmpXchgConst(ref)
            // case LLVMAtomicRMW      => AtomicRMWConst(ref)
            // case LLVMResume         => ResumeConst(ref)
            // case LLVMLandingPad     => LandingPadConst(ref)
            // case LLVMCleanupRet     => CleanupRetConst(ref)
            // case LLVMCatchRet       => CatchRetConst(ref)
            // case LLVMCatchPad       => CatchPadConst(ref)
            // case LLVMCleanupPad     => CleanupPadConst(ref)
            // case LLVMCatchSwitch    => CatchSwitchConst(ref)
            case opCode            => throw new IllegalArgumentException("unknown instruction opcode: "+opCode)
        }
    }
}

sealed abstract class ConstantExpression(ref: LLVMValueRef) extends User(ref)

// // case class RetConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class BrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SwitchConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class IndirectBrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class InvokeConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class UnreachableConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CallBrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FNegConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AddConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FAddConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SubConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FSubConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class MulConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FMulConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class UDivConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SDivConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FDivConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class URemConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SRemConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FRemConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ShlConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class LShrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AShrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AndConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class OrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class XorConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AllocaConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class LoadConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class StoreConst(ref: LLVMValueRef) extends ConstantExpression(ref)
case class GetElementPtrConst(ref: LLVMValueRef) extends ConstantExpression(ref) {
    def base: Value = operand(0)
    def isConstant = (1 until numOperands).forall(operand(_).isInstanceOf[ConstantIntValue])
    def constants = (1 until numOperands).map(operand(_).asInstanceOf[ConstantIntValue].signExtendedValue)
    def isZero = isConstant && constants.forall(_ == 0)
}
// case class TruncConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ZExtConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SExtConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FPToUIConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FPToSIConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class UIToFPConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SIToFPConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FPTruncConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FPExtConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class PtrToIntConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class IntToPtrConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class BitCastConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AddrSpaceCastConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ICmpConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FCmpConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class PHIConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CallConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class SelectConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class UserOp1Const(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class UserOp2Const(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class VAArgConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ExtractElementConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class InsertElementConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ShuffleVectorConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ExtractValueConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class InsertValueConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FreezeConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class FenceConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AtomicCmpXchgConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class AtomicRMWConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class ResumeConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class LandingPadConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CleanupRetConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CatchRetConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CatchPadConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CleanupPadConst(ref: LLVMValueRef) extends ConstantExpression(ref)
// case class CatchSwitchConst(ref: LLVMValueRef) extends ConstantExpression(ref)
