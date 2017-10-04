# Cell PPU test code.
# Written by Andrew Church <achurch@achurch.org>
# No copyright is claimed on this file.
#
# Update history:
#    - 2016-10-22: Applied several fixes and changes from the PowerPC 750CL
#         test suite at <http://achurch.org/cpu-tests/ppc750cl.s>:
#         - Fixed cases in which mtcrf tests could leave blank failure
#              records.
#         - Made the icbi test a little more semantically sensible.
#         - Added tests to verify that lmw/stmw with a very positive offset
#              do not wrap around to negative offsets.  Also changed the
#              lmw/stmw tests to record the incorrect value detected and
#              the associated register index in words 2 and 3 of the
#              failure record.
#         - Added a test to verify that lwarx followed by stwcx. on a
#              different address still succeeds.
#         - Added a test for blrl to verify that LR is read and written in
#              the correct order.
#    - 2016-01-29: Fixed incorrect encoding of "bc 31,2,target".
#         Thanks to Matt Mastracci for spotting the error.
#    - 2015-12-15: Added tests for various floating-point edge cases.
#    - 2015-12-13: Added tests verifying behavior of single-precision
#         floating-point instructions on double-precision operands.
#    - 2015-12-11: Added a test verifying that fsel does not generate
#         exceptions for SNaN inputs.
#    - 2015-12-11: Fixed a logic error in the fres and frsqrte tests which
#         could have caused the tests to erroneously pass.
#    - 2015-12-11: Added tests verifying that overflow of the intermediate
#         product in a fused multiply-add instruction does not result in a
#         VXISI exception.
#    - 2015-12-11: Added tests verifying that "fmadd frD,0,inf,SNaN" (and
#         fmsub, fnmadd, fnmsub) raises both VXSNAN and VXIMZ exceptions.
#    - 2015-12-11: Failure records are now cleared to zero for every test,
#         so data provisionally stored during a previous test does not
#         pollute the results.
#    - 2015-12-10: Added tests verifying that loading and storing -0.0 in
#         floating-point registers does not change the sign of the value.
#    - 2015-12-10: Tweaked the fmr./fneg./fabs./fnabs. tests to reduce the
#         chance of spuriously passing by explicitly setting FPSCR[0:3].
#    - 2015-12-08: Added tests verifying that floating-point instructions
#         which can set exception flags do not clear those flags after an
#         operation which does not generate an exception.
#    - 2015-12-08: Added tests for exception handling in fcmpu/fcmpo,
#         verifying that exception bits are set in each relevant case.
#         Also fixed a logic bug preventing FPSCR from being properly
#         stored in failure records.
#    - 2015-12-08: Added tests for floating-point instructions verifying
#         that FX is not set when a set exception bit in FPSCR is already 1.
#    - 2015-12-07: Manually coded the mftb and mftbu instructions to work
#         around a bug in the GNU binutils assembler.
#    - 2015-12-07: Miscellaneous code cleanup: changed some lwa
#         instructions to lwz where lwa was not specifically necessary,
#         and tweaked some code sequences to simplify porting to 32-bit
#         PowerPC architectures.
#    - 2015-12-07: Moved the get_load_address subroutine inside .if TEST_BA
#         since it is unnecessary when absolute branches are not tested.
#    - 2015-01-17: Added additional test cases for vmaxfp and vminfp which
#         cover comparisons between NaNs and normal numbers.
#    - 2015-01-17: The mftbu test now records the values read from both the
#         TBH and TBL registers on failure.
#    - 2015-01-17: Fixed cases in which FPU tests could report the wrong
#         FPSCR value on failure (the tests themselves behaved properly).
#    - 2015-01-17: Fixed some FPU tests which could incorrectly pass even
#         if FPSCR was improperly updated on aborted operations.
#    - 2015-01-17: Added tests for exception handling in FPU instructions
#         with Rc=1, verifying that CR1 is updated even if the operation
#         itself is aborted.
#    - 2015-01-17: ALU instruction tests now record XER along with CR on
#         failure.
#    - 2014-09-21: Fixed an infinite loop if bdzlr is broken.
#    - 2014-09-19: Added tests for behavior of the addic[.] instructions
#         when the XER[CA] flag is set.
#    - 2014-09-19: Fixed behavior when XER[CA] is set on entry.
#    - 2014-09-07: Added tests for mfvrsave and mtvrsave.
#    - 2014-08-28: Initial release.
#
# This file implements a test routine which exercises all instructions
# implemented by the Cell Broadband Engine's PPU and verifies that they
# return correct results.  The routine (excluding the tests of the trap
# and system call instructions) has been validated against a real Cell
# processor.
#
# Call with four arguments:
#    R3: 0 (to bootstrap a constant value into the register file)
#    R4: pointer to a 32k (32768-byte) pre-cleared, cache-aligned scratch
#           memory block (must not be address zero)
#    R5: pointer to a memory block into which failing instructions will be
#           written (should be at least 64k to avoid overruns)
#    F1: 1.0 (for register file bootstrapping)
# This follows the PowerPC ABI and can be called from C code with a
# prototype like:
#     extern int test(int zero, void *scratch, void *failures, double one);
# (Note that this file does not itself define a symbol for the beginning
# of the test routine.  You can edit this file to insert such a symbol, or
# include this file in another file immediately after a symbol definition.)
#
# Returns (in R3) the number of failing instructions, or a negative value
# if the test failed to bootstrap itself.
#
# On return, if R3 > 0 then the buffer in R5 contains R3 failure records.
# Each failure record is 8 words (32 bytes) long and has the following
# format:
#    Word 0: Failing instruction word
#    Word 1: Address of failing instruction word
#    Words 2-7: Auxiliary data (see below)
# Instructions have been coded so that generally, the operands uniquely
# identify the failing instruction, but in some cases (such as rounding
# mode tests with frsp) there are multiple copies of the same instruction
# in different locations; in such cases, use the address to locate the
# failing instruction.
#
# The "auxiliary data" stored in a failure record varies by instruction
# (see the code around the failure point for details), but it is usually
# the value produced by the failing instruction, with integer and
# floating-point values stored to words 2-3 of the failure record and
# vector values stored to words 4-7.  In particular, instructions checked
# by the check_alu_* and check_fpu_* subroutines store the incorrect result
# as a doubleword (or double-precision floating point value) in words 2-3,
# the value of CR (or FPSCR) as a doubleword in words 4-5, and (for
# check_alu_* only) the value of XER as a doubleword in words 6-7, while
# the check_vector_* subroutines store the value of CR in word 2, the value
# of VSCR in word 3, and the incorrect result in words 4-7.
#
# The code assumes that the following instructions work correctly:
#    - beq cr0,target
#    - bne cr0,target
#    - bl
#    - blr (bclr 20,0,0)
#    - fcmpu (to the extent that two FP registers can be tested for equality)
#    - mflr
#    - mtlr
#
# The following instructions and features are not tested:
#    - The bca and bcla instructions
#    - D-form and DS-form loads and stores to absolute addresses (RA=0)
#    - Floating-point operations with FPSCR[OE] or FPSCR[UE] set
#    - The effect of floating-point operations on FPSCR[FR]
#    - Graphics mode for vector instructions (HID1[grap_mode]=1)
#

# MFTB_SPIN_COUNT:  Set this to the number of times to loop while waiting
# for the time base register to increment.
.ifndef MFTB_SPIN_COUNT
MFTB_SPIN_COUNT = 256
.endif

# TEST_BA:  Set this to 1 to test the ba and bla (branch absolute)
# instructions.  For these tests to work, the code must be loaded at
# absolute address 0x1000000.  (If this option is enabled and the code
# is loaded at the wrong address, the bootstrap will fail with return
# value -256 in R3 and the detected load address in R4.)
.ifndef TEST_BA
TEST_BA = 0
.endif

# TEST_SC:  Set this to 1 to test the sc (system call) instruction.  The
# implementation should set R3 to the value of the instruction's LEV
# operand and resume execution at the next instruction.
.ifndef TEST_SC
TEST_SC = 0
.endif

# TEST_TRAP:  Set this to 1 to test the tdi, twi, td, and tw (trap)
# instructions.  The implementation should set R3 to the value zero and
# resume execution at the next instruction.
.ifndef TEST_TRAP
TEST_TRAP = 0
.endif

# Convenience macros to load a 32-bit value into the low word (lvi) or all
# words (lvia) of a vector register.  Destroys 0x7000..0x700F(%r4) and %r10.

.macro lvi vd,imm
   li %r10,0
   stw %r10,0x7000(%r4)
   stw %r10,0x7004(%r4)
   stw %r10,0x7008(%r4)
.if (\imm >= -0x8000) && (\imm <= 0x7FFF)
   li %r10,\imm
.else
   lis %r10,\imm >> 16
.if \imm & 0xFFFF
   ori %r10,%r10,\imm & 0xFFFF
.endif
.endif
   stw %r10,0x700C(%r4)
   li %r10,0x7000
   lvx \vd,%r10,%r4
.endm

.macro lvia vd,imm
.if (\imm >= -0x8000) && (\imm <= 0x7FFF)
   li %r10,\imm
.else
   lis %r10,\imm >> 16
.if \imm & 0xFFFF
   ori %r10,%r10,\imm & 0xFFFF
.endif
.endif
   stw %r10,0x7000(%r4)
   stw %r10,0x7004(%r4)
   stw %r10,0x7008(%r4)
   stw %r10,0x700C(%r4)
   li %r10,0x7000
   lvx \vd,%r10,%r4
.endm

# Convenience macros to load or store a vector register using an immediate
# offset.  Destroys %r10.

.macro lv vd,imm,rb
.if \imm
   li %r10,\imm
   lvx \vd,%r10,\rb
.else
   lvx \vd,0,\rb
.endif
.endm

.macro stv vd,imm,rb
.if \imm
   li %r10,\imm
   stvx \vd,%r10,\rb
.else
   stvx \vd,0,\rb
.endif
.endm

# Workaround for older assemblers that don't understand vmr and vnot.

.macro vmr vd,vb
   vor \vd,\vb,\vb
.endm

.macro vnot vd,vb
   vnor \vd,\vb,\vb
.endm


.machine ppu
.text
.global .test

.test:

   ########################################################################
   # Jump over a couple of tests which need to be located at a known
   # address when testing absolute branch instructions.  As we do so,
   # check that cmpdi against zero works.
   ########################################################################

0: cmpdi %r3,0          # 0x1000000
   beq 0f               # 0x1000004
   li %r3,-1            # 0x1000008
   blr                  # 0x100000C

.if TEST_BA

   ########################################################################
   # Subroutine called from the bootstrap code to verify the load address.
   # Returns the load address of the test code (label 0b above) in R3;
   # destroys R0.
   ########################################################################

get_load_address:
   mflr %r0             # 0x1000010
   bl 1f                # 0x1000014
1: mflr %r3             # 0x1000018
   mtlr %r0             # 0x100001C
   addi %r3,%r3,0b-1b   # 0x1000020
   blr                  # 0x1000024

   ########################################################################
   # 2.4.1 Branch Instructions - ba, bla (second half of test)
   ########################################################################

   mflr %r3             # 0x1000028
   ba 0x1000038         # 0x100002C
   # These two instructions should be skipped.
   bl record            # 0x1000030
   addi %r6,%r6,32      # 0x1000034
   # Execution continues here.
   addi %r3,%r3,8       # 0x1000038
   mtlr %r3             # 0x100003C
   blr                  # 0x1000040

.endif  # TEST_BA

   ########################################################################
   # Bootstrap a few instructions so we have a little more flexibility.
   ########################################################################

   # mr RT,RA (or RT,RA,RA)
0: mr %r0,%r3       # Zero value.
   cmpdi %r0,0
   beq 0f
   li %r3,-2
   blr
0: mr %r0,%r4       # Nonzero value.
   cmpdi %r0,0
   bne 0f
   li %r3,-3
   blr

   # li RT,0 (addi RT,0,0)
0: li %r0,0
   cmpdi %r0,0
   beq 0f
   li %r3,-4
   blr

   # li RT,imm (addi RT,0,imm), positive value
0: li %r0,1
   cmpdi %r0,0
   bne 0f
   li %r3,-5
   blr

   # lis RT,imm (addis RT,0,imm), positive value
0: li %r0,0
   lis %r0,1
   cmpdi %r0,0
   bne 0f
   li %r3,-6
   blr

   # b target (forward displacement)
0: b 0f
   li %r3,-7
   blr

   # cmpd RA,RB (cmp 0,0,RA,RB)
0: cmpd %r0,%r0
   beq 0f
   li %r3,-8
   blr
0: cmpd %r0,%r3
   bne 0f
   li %r3,-9
   blr

   # cmpdi RA,imm (cmpi 0,1,RA,imm) with imm != 0
0: li %r0,1
   cmpdi %r0,1
   beq 0f
   li %r3,-10
   blr

   # addi RT,RT,imm (RT != 0, imm > 0)
0: mr %r3,%r0
   addi %r3,%r3,2
   cmpdi %r3,3
   beq 0f
   li %r3,-11
   blr

   # addi RT,RT,imm (RT != 0, imm < 0)
0: addi %r3,%r3,-1
   cmpdi %r3,2
   beq 0f
   li %r3,-12
   blr

   # addi RT,RA,imm (RT != RA)
0: addi %r7,%r3,2
   cmpdi %r7,4
   beq 0f
   li %r3,-13
   blr

   # addis RT,RA,imm
0: lis %r7,1
   addis %r3,%r7,2
   lis %r7,3
   cmpd %r3,%r7
   beq 0f
   li %r3,-14
   blr

   # lwz RT,0(RA)
0: lwz %r0,0(%r4)
   cmpdi %r0,0
   beq 0f
   li %r3,-15
   blr

   # stw RS,0(RA)
0: li %r0,1
   stw %r0,0(%r4)
   li %r0,0
   lwz %r0,0(%r4)
   cmpdi %r0,1
   beq 0f
   li %r3,-16
   blr

   # lwz RT,imm(RA) (imm > 0)
   # stw RS,imm(RA) (imm > 0)
0: li %r0,2
   stw %r0,8(%r4)
   li %r0,0
   lwz %r0,8(%r4)
   cmpdi %r0,2
   beq 0f
   li %r3,-17
   blr

   # lwz RT,imm(RA) (imm < 0)
   # stw RS,imm(RA) (imm < 0)
0: addi %r3,%r4,16
   li %r0,3
   stw %r0,-12(%r3)
   li %r0,0
   lwz %r0,-12(%r3)
   cmpdi %r0,3
   beq 0f
   li %r3,-18
   blr
0: li %r0,0
   lwz %r0,4(%r4)
   cmpdi %r0,3
   beq 0f
   li %r3,-19
   blr

   ########################################################################
   # If we'll be testing the absolute branch instructions, ensure that the
   # test code was loaded at the correct address.
   ########################################################################

.if TEST_BA
0: mflr %r7
   bl get_load_address
   mtlr %r7
   lis %r7,0x100
   cmpd %r3,%r7
   beq 0f
   mr %r4,%r3
   li %r3,-256
   blr
.endif

   ########################################################################
   # Save nonvolatile registers used in the test.
   ########################################################################

0: mfcr %r0
   stw %r0,0x7EE4(%r4)
   mflr %r0
   std %r0,0x7EE8(%r4)
   std %r24,0x7EF0(%r4)
   std %r25,0x7EF8(%r4)
   std %r26,0x7F00(%r4)
   std %r27,0x7F08(%r4)
   std %r28,0x7F10(%r4)
   std %r29,0x7F18(%r4)
   std %r30,0x7F20(%r4)
   std %r31,0x7F28(%r4)
   stfd %f14,0x7F30(%r4)
   stfd %f15,0x7F38(%r4)
   stfd %f24,0x7F40(%r4)
   stfd %f25,0x7F48(%r4)
   stfd %f26,0x7F50(%r4)
   stfd %f27,0x7F58(%r4)
   stfd %f28,0x7F60(%r4)
   stfd %f29,0x7F68(%r4)
   stfd %f30,0x7F70(%r4)
   stfd %f31,0x7F78(%r4)
   stv %v24,0x7F80,%r4
   stv %v25,0x7F90,%r4
   stv %v26,0x7FA0,%r4
   stv %v27,0x7FB0,%r4
   stv %v28,0x7FC0,%r4
   stv %v29,0x7FD0,%r4
   stv %v30,0x7FE0,%r4
   stv %v31,0x7FF0,%r4

   ########################################################################
   # Set up some registers used in the test proper:
   #     R6 = pointer to next slot in failed-instruction buffer
   ########################################################################

   mr %r6,%r5

   ########################################################################
   # Beginning of the test proper.  The test is divided into sections,
   # each with a header comment (like this one) which indicates the group
   # of instructions being tested.  Where applicable, the header also
   # indicates the reference material used to write the tests:
   #
   # - "X.Y.Z Section Title" (where X, Y, Z are numbers): the given section
   #   in "PowerPC User Instruction Set Architecture, Book I, Version 2.02"
   #
   # - "Book II X.Y.Z Section Title": the given section in "PowerPC Virtual
   #   Environment Architecture, Book II, Version 2.02"
   #
   # - "Vector Processing Instructions": the instruction descriptions in
   #   "PowerPC Microprocessor Family: Vector/SIMD Multimedia Extension
   #   Technology Programming Environments Manual, Version 2.07c"
   ########################################################################

   ########################################################################
   # 2.4.1 Branch Instructions - b, bl
   ########################################################################

   # b (forward displacement) was tested in the bootstrap code.

   # bl (forward displacement)
0: bl 3f
1: bl record
   lwz %r3,(2f-1b)(%r3)
   lis %r0,1
   cmpd %r0,%r3
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
   b 0f
2: .int 0x00010000
3: mflr %r3
   blr

   # b (backward displacement)
0: b 1f
2: b 0f
1: b 2b
   bl record
   addi %r6,%r6,32

   # bl (backward displacement)
0: b 2f
1: mflr %r3
   blr
2: bl 1b
3: bl record
   lwz %r3,(4f-3b)(%r3)
   lis %r0,2
   cmpd %r0,%r3
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
   b 0f
4: .int 0x00020000

   ########################################################################
   # 2.4.1 Branch Instructions - ba, bla (first half of test)
   ########################################################################

.if TEST_BA
0: bla 0x1000028
   bl record        # Skipped.
   addi %r6,%r6,32  # Skipped.
.endif

   ########################################################################
   # 2.4.1 Branch Instructions - bc (decrement CTR and branch if zero)
   # 3.3.13 Move To/From System Register Instructions - mtctr, mfctr
   ########################################################################

   # Single iteration (CTR=1 -> 0)
   li %r3,1
   mtctr %r3
   bdz 0f
   bl record
   addi %r6,%r6,32

   # Two iterations (CTR=2 -> 1 -> 0)
0: li %r3,2
   mtctr %r3
   bl record
   bdz 1f           # Not taken.
   mfctr %r3
   bl record
   cmpdi %r3,1
   beq 2f
   std %r3,8(%r6)
   addi %r6,%r6,32
2: bdz 0f           # Taken.
   bl record
1: addi %r6,%r6,32

   ########################################################################
   # 2.4.1 Branch Instructions - bc
   ########################################################################

   # bc 1z1zz,BI,target (branch always)
   # We set up CR0 here for the "eq" condition and leave it untouched for
   # all of these tests.
0: li %r3,0
   cmpdi %r3,0
   # Test with a false CR bit.
   bc 20,0,0f
   bl record
   addi %r6,%r6,32
   # Some assemblers reject instructions with z != 0, so code them directly.
0: .int 0x42A0000C  # bc 21,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x42C0000C  # bc 22,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x42E0000C  # bc 23,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x4380000C  # bc 28,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43A0000C  # bc 29,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43C0000C  # bc 30,0,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43E0000C  # bc 31,0,0f
   bl record
   addi %r6,%r6,32
   # Test with a true CR bit.
0: bc 20,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x42A2000C  # bc 21,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x42C2000C  # bc 22,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x42E2000C  # bc 23,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x4382000C  # bc 28,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43A2000C  # bc 29,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43C2000C  # bc 30,2,0f
   bl record
   addi %r6,%r6,32
0: .int 0x43E2000C  # bc 31,2,0f
   bl record
   addi %r6,%r6,32

   # bc 1a01t,BI,target (decrement and branch if CTR==0)
0: li %r3,2
   mtctr %r3
   bdz 1f           # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdz 0f           # Taken.
   bl record
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   bdz- 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdz- 0f          # Taken.
   bl record
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   bdz+ 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdz+ 0f          # Taken.
   bl record
   addi %r6,%r6,32

   # bc 1a00t,BI,target (decrement and branch if CTR!=0)
0: li %r3,1
   mtctr %r3
   bdnz 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnz 0f          # Taken.
   bl record
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   bdnz- 1f         # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnz- 0f         # Taken.
   bl record
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   bdnz+ 1f         # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnz+ 0f         # Taken.
   bl record
   addi %r6,%r6,32

   # bc 011at,BI,target (branch if condition bit true)
0: bgt 1f           # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: beq 0f           # Taken.
   bl record
   addi %r6,%r6,32
0: bgt- 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: beq- 0f          # Taken.
   bl record
   addi %r6,%r6,32
0: bgt+ 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: beq+ 0f          # Taken.
   bl record
   addi %r6,%r6,32

   # bc 0101z,BI,target (decrement and branch if condition true and CTR==0)
0: li %r3,2
   mtctr %r3
   bdzt gt,1f       # Not taken (condition false and CTR!=0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdzt gt,1f       # Not taken (condition false).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   bdzt eq,1f       # Not taken (CTR!=0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdzt eq,0f       # Taken.
   bl record
   addi %r6,%r6,32
   # Same with z=1.
0: li %r3,2
   mtctr %r3
   .int 0x41610008  # bdzt gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x41610008  # bdzt gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   .int 0x41620008  # bdzt eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x4162000C  # bdzt eq,0f
   bl record
   addi %r6,%r6,32

   # bc 0100z,BI,target (decrement and branch if condition true and CTR!=0)
0: li %r3,1
   mtctr %r3
   bdnzt gt,1f      # Not taken (condition false and CTR==0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnzt gt,1f      # Not taken (condition false).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   bdnzt eq,1f      # Not taken (CTR==0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnzt eq,0f      # Taken.
   bl record
   addi %r6,%r6,32
   # Same with z=1.
0: li %r3,1
   mtctr %r3
   .int 0x41210008  # bdzt gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x41210008  # bdzt gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   .int 0x41220008  # bdzt eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x4122000C  # bdzt eq,0f
   bl record
   addi %r6,%r6,32

   # bc 001at,BI,target (branch if condition bit false)
0: bne 1f           # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: ble 0f           # Taken.
   bl record
   addi %r6,%r6,32
0: bne- 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: ble- 0f          # Taken.
   bl record
   addi %r6,%r6,32
0: bne+ 1f          # Not taken.
   b 0f
1: bl record2
   addi %r6,%r6,32
0: ble+ 0f          # Taken.
   bl record
   addi %r6,%r6,32

   # bc 0001z,BI,target (decrement and branch if condition false and CTR==0)
0: li %r3,2
   mtctr %r3
   bdzf eq,1f       # Not taken (condition false and CTR!=0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdzf eq,1f       # Not taken (condition false).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   bdzf gt,1f       # Not taken (CTR!=0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdzf gt,0f       # Taken.
   bl record
   addi %r6,%r6,32
   # Same with z=1.
0: li %r3,2
   mtctr %r3
   .int 0x40620008  # bdzf eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x40620008  # bdzf eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,2
   mtctr %r3
   .int 0x40610008  # bdzf gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x4061000C  # bdzf gt,0f
   bl record
   addi %r6,%r6,32

   # bc 0000z,BI,target (decrement and branch if condition false and CTR!=0)
0: li %r3,1
   mtctr %r3
   bdnzf eq,1f      # Not taken (condition false and CTR==0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnzf eq,1f      # Not taken (condition false).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   bdnzf gt,1f      # Not taken (CTR==0).
   b 0f
1: bl record2
   addi %r6,%r6,32
0: bdnzf gt,0f      # Taken.
   bl record
   addi %r6,%r6,32
   # Same with z=1.
0: li %r3,1
   mtctr %r3
   .int 0x40220008  # bdzf eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x40220008  # bdzf eq,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: li %r3,1
   mtctr %r3
   .int 0x40210008  # bdzf gt,1f
   b 0f
1: bl record2
   addi %r6,%r6,32
0: .int 0x4021000C  # bdzf gt,0f
   bl record
   addi %r6,%r6,32

   # bc (backward displacement)
   # We assume the displacement and link flags are processed the same way
   # for all conditions, so we only test a single condition here and below.
0: b 1f
2: b 0f
1: bc 20,0,2b
   bl record
   addi %r6,%r6,32  # Skipped.

   # bcl
0: bcl 20,0,3f
1: bl record
   lwz %r3,(2f-1b)(%r3)
   lis %r0,3
   cmpd %r0,%r3
   beq 0f
   addi %r6,%r6,32
   b 0f
2: .int 0x00030000
3: mflr %r3
   blr

   # Testing bca/bcla requires a system in which the address range
   # -0x8000...0x7FFF is mapped.  Such systems are believed to be rare if
   # not nonexistent, so we skip those instructions.

   ########################################################################
   # 2.4.1 Branch Instructions - bclr, bcctr
   ########################################################################

   # We assume bclr and bcctr use the same condition decoding logic as bc,
   # so we only use one test for each different instruction pattern.

   # bclr (with decrement)
0: b 2f
1: li %r0,2
   mtctr %r0
   bdzlr
   bdzlr
   bdzlr
   blr
2: bl record2
   bl 1b
3: mfctr %r3
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # bclr (with condition)
0: b 2f
1: li %r0,2
   cmpdi %r0,2
   beqlr
   mflr %r0
   bl record2
   mtlr %r0
   addi %r6,%r6,32
   blr
2: bl 1b

   # blrl (unconditional) -- check that this jumps to the previous value of
   # LR, not the value written by this instruction.
0: bl 4f                # Get the address of the next instruction so we can
1: addi %r3,%r3,3f-1b   # compute the address of label 3f to store in LR.
   addi %r7,%r3,2f-1b   # Also get the expected return address.
   mtlr %r3
   blrl                 # Jumps to label 3f.
2: bl record            # Fallthrough means we jumped to the new LR.
   addi %r6,%r6,32
   b 0f
3: mflr %r3
   cmpw %r3,%r7
   beq 0f
   addi %r9,%r7,-4
   lwz %r8,0(%r9)
   stw %r8,0(%r6)
   stw %r9,4(%r6)
   stw %r3,8(%r6)
   li %r8,0
   stw %r8,12(%r6)
   stw %r8,16(%r6)
   stw %r8,20(%r6)
   b 0f
4: mflr %r3
   blr

   # bcctr (unconditional)
0: bl 2f
1: addi %r3,%r3,0f-1b
   mtctr %r3
   bctr                 # Jumps to label 0f.
   bl record
   addi %r6,%r6,32
   b 0f
2: mflr %r3
   blr

   # bcctr (with condition)
0: bl 2f
1: addi %r3,%r3,0f-1b
   mtctr %r3
   li %r0,2
   cmpdi %r0,2
   beqctr
   bl record
   addi %r6,%r6,32
   b 0f
2: mflr %r3
   blr

   ########################################################################
   # 2.4.2 System Call Instruction
   ########################################################################

.if TEST_SC

0: li %r3,-1
   sc
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   sc 1
   bl record
   cmpdi %r3,1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

.endif  # TEST_SC


   ########################################################################
   # 3.3.13 Move To/From System Register Instructions - mtcrf, mfcr
   ########################################################################

   # mtcr (mtcrf 255,RS)
0: li %r3,0
   cmpdi %r3,0
   mtcr %r3
   bl record
   bne 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mfcr
0: li %r3,0
   cmpdi %r3,0
   mfcr %r3
   bl record
   lis %r0,0x2000
   cmpd %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtcrf (single field)
0: lis %r3,0x4000
   mtcrf 128,%r3
   bl record
   bgt 0f
   addi %r6,%r6,32
0: lis %r3,0x0200
   mtcrf 64,%r3
   bl record
   ble 1f
   beq cr1,0f
1: addi %r6,%r6,32

   ########################################################################
   # 2.4.3 Condition Register Logical Instructions
   ########################################################################

   # crand
0: li %r3,0x0123
   mtcr %r3
   crand 17,20,24   # 0 & 0
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crand 17,20,26   # 0 & 1
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crand 17,23,24   # 1 & 0
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crand 17,23,26   # 1 & 1
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crand 31,31,31   # Check for inputs getting clobbered by output.
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # cror
0: li %r3,0x0123
   mtcr %r3
   cror 17,20,24   # 0 | 0
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   cror 17,20,26   # 0 | 1
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   cror 17,23,24   # 1 | 0
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   cror 17,23,26   # 1 | 1
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   cror 31,31,31
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # crxor
0: li %r3,0x0123
   mtcr %r3
   crxor 17,20,24   # 0 ^ 0
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crxor 17,20,26   # 0 ^ 1
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crxor 17,23,24   # 1 ^ 0
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crxor 17,23,26   # 1 ^ 1
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crxor 31,31,17
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crxor 31,17,31
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # crnand
0: li %r3,0x0123
   mtcr %r3
   crnand 17,20,24   # ~(0 & 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 17,20,26   # ~(0 & 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 17,23,24   # ~(1 & 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 17,23,26   # ~(1 & 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 17,17,17
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # crnor
0: li %r3,0x0123
   mtcr %r3
   crnor 17,20,24   # ~(0 | 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnor 17,20,26   # ~(0 | 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnor 17,23,24   # ~(1 | 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnor 17,23,26   # ~(1 | 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnor 17,17,17
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # creqv
0: li %r3,0x0123
   mtcr %r3
   creqv 17,20,24   # ~(0 ^ 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   creqv 17,20,26   # ~(0 ^ 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   creqv 17,23,24   # ~(1 ^ 0)
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   creqv 17,23,26   # ~(1 ^ 1)
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   creqv 17,17,17
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # crandc
0: li %r3,0x0123
   mtcr %r3
   crandc 17,20,24   # 0 & ~0
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crandc 17,20,26   # 0 & ~1
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crandc 17,23,24   # 1 & ~0
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crandc 17,23,26   # 1 & ~1
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 31,31,17
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crnand 17,31,17
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # crorc
0: li %r3,0x0123
   mtcr %r3
   crorc 17,20,24   # 0 | ~0
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crorc 17,20,26   # 0 | ~1
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crorc 17,23,24   # 1 | ~0
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crorc 17,23,26   # 1 | ~1
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0x0123
   mtcr %r3
   crorc 17,17,17
   bl record
   mfcr %r3
   cmpdi %r3,0x4123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 2.4.4 Condition Register Field Instruction
   ########################################################################

   # mcrf
0: li %r3,0x0123
   mtcr %r3
   mcrf 4,7
   bl record
   mfcr %r3
   cmpdi %r3,0x3123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
   # Check that the CR field is not cleared for overwrite before it is read.
0: li %r3,0x0123
   mtcr %r3
   mcrf 5,5
   bl record
   mfcr %r3
   cmpdi %r3,0x0123
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.2 Fixed-Point Load Instructions - lbz, lhz, lha, lwz, lwa (and -x, -u, -ux forms)
   ########################################################################

0: lis %r3,0xCE02
   addi %r3,%r3,0x468A
   stw %r3,0(%r4)
   lis %r3,0xDF13
   addi %r3,%r3,0x579B
   stw %r3,4(%r4)

   # lbz
0: addi %r7,%r4,2
   mr %r0,%r7
   lbz %r3,-2(%r7)
   bl record
   cmpdi %r3,0xCE
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lbz %r3,-1(%r7)
   bl record
   cmpdi %r3,0x02
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lbz %r3,0(%r7)
   bl record
   cmpdi %r3,0x46
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lbz %r3,1(%r7)
   bl record
   cmpdi %r3,0x8A
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lbzx
0: addi %r7,%r4,2
   mr %r0,%r7
   li %r11,-2
   lbzx %r3,%r7,%r11
   bl record
   cmpdi %r3,0xCE
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
   # Also check the case where RA=0 (should use 0 instead of the value of r0).
0: li %r3,0
   li %r0,1
   lbzx %r3,0,%r4
   bl record
   cmpdi %r3,0xCE
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lbzu
0: addi %r7,%r4,2
   lbzu %r3,-2(%r7)
   bl record
   cmpdi %r3,0xCE
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lbzux
0: addi %r7,%r4,2
   li %r11,-2
   lbzux %r3,%r7,%r11
   bl record
   cmpdi %r3,0xCE
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lhz
0: addi %r7,%r4,2
   mr %r0,%r7
   lhz %r3,-2(%r7)
   bl record
   li %r11,0x6E02
   addi %r11,%r11,0x6000
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lhz %r3,0(%r7)
   bl record
   cmpdi %r3,0x468A
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lhzx
0: addi %r7,%r4,2
   mr %r0,%r7
   li %r11,-2
   lhzx %r3,%r7,%r11
   bl record
   li %r11,0x6E02
   addi %r11,%r11,0x6000
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,2
   lhzx %r3,0,%r4
   bl record
   li %r11,0x6E02
   addi %r11,%r11,0x6000
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lhzu
0: addi %r7,%r4,2
   lhzu %r3,-2(%r7)
   bl record
   li %r11,0x6E02
   addi %r11,%r11,0x6000
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lhzux
0: addi %r7,%r4,2
   li %r11,-2
   lhzux %r3,%r7,%r11
   bl record
   li %r11,0x6E02
   addi %r11,%r11,0x6000
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lha
0: addi %r7,%r4,2
   mr %r0,%r7
   lha %r3,-2(%r7)
   bl record
   cmpdi %r3,0xCE02-0x10000
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: addi %r6,%r6,32
0: lha %r3,0(%r7)
   bl record
   cmpdi %r3,0x468A
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lhax
0: addi %r7,%r4,2
   mr %r0,%r7
   li %r11,-2
   lhax %r3,%r7,%r11
   bl record
   cmpdi %r3,0xCE02-0x10000
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,2
   lhax %r3,0,%r4
   bl record
   cmpdi %r3,0xCE02-0x10000
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lhau
0: addi %r7,%r4,2
   lhau %r3,-2(%r7)
   bl record
   cmpdi %r3,0xCE02-0x10000
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lhaux
0: addi %r7,%r4,2
   li %r11,-2
   lhaux %r3,%r7,%r11
   bl record
   cmpdi %r3,0xCE02-0x10000
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lwz was tested in the bootstrap code.

   # lwzx
0: addi %r7,%r4,4
   mr %r0,%r7
   li %r11,-4
   lwzx %r3,%r7,%r11
   bl record
   lis %r11,0x6E02
   addis %r11,%r11,0x6000
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,4
   lwzx %r3,0,%r4
   bl record
   lis %r11,0x6E02
   addis %r11,%r11,0x6000
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lwzu
0: addi %r7,%r4,4
   lwzu %r3,-4(%r7)
   bl record
   lis %r11,0x6E02
   addis %r11,%r11,0x6000
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lwzux
0: addi %r7,%r4,4
   li %r11,-4
   lwzux %r3,%r7,%r11
   bl record
   lis %r11,0x6E02
   addis %r11,%r11,0x6000
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lwa
0: addi %r7,%r4,4
   mr %r0,%r7
   lwa %r3,-4(%r7)
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lwa %r3,0(%r7)
   bl record
   lis %r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lwax
0: addi %r7,%r4,4
   mr %r0,%r7
   li %r11,-4
   lwax %r3,%r7,%r11
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,4
   lwax %r3,0,%r4
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lwaux
0: addi %r7,%r4,4
   li %r11,-4
   lwaux %r3,%r7,%r11
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.11 Fixed-Point Logical Instructions - oris
   ########################################################################

   # oris
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   addi %r3,%r3,0x0006
   li %r7,6
   oris %r7,%r7,0xC000
   bl record
   cmpd %r7,%r3
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.12.2 Fixed-Point Rotate and Shift Instructions - sld, srd (count < 64)
   ########################################################################

   # srd
0: li %r0,36
   li %r3,-1
   srd %r3,%r3,%r0
   bl record
   lis %r7,0x1000
   addi %r7,%r7,-1
   cmpd %r3,%r7
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # sld
0: li %r0,40
   lis %r3,0x1000
   addi %r3,%r3,-2
   sld %r3,%r3,%r0
   bl record
   li %r0,36
   srd %r3,%r3,%r0
   lis %r7,0x1000
   addi %r7,%r7,-32
   cmpd %r3,%r7
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.2 Fixed-Point Load Instructions - ld, ldx, ldu, ldux
   ########################################################################

   # ld
0: addi %r7,%r4,4
   mr %r0,%r7
   ld %r3,-4(%r7)
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   ld %r3,0(%r4)
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # ldx
0: addi %r7,%r4,4
   mr %r0,%r7
   li %r11,-4
   ldx %r3,%r7,%r11
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,2
   ldx %r3,0,%r4
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # ldu
0: addi %r7,%r4,4
   ldu %r3,-4(%r7)
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # ldux
0: addi %r7,%r4,4
   li %r11,-4
   ldux %r3,%r7,%r11
   bl record
   lis %r11,0xCE02
   addi %r11,%r11,0x468A
   li %r8,32
   sld %r11,%r11,%r8
   oris %r11,%r11,0xDF13
   addi %r11,%r11,0x579B
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.3 Fixed-Point Store Instructions
   ########################################################################

   # stb
0: li %r3,0
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   addi %r7,%r4,2
   mr %r0,%r7
   li %r3,0xCE
   stb %r3,-2(%r7)
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0xCE00-0x10000
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0x02
   stb %r3,-1(%r7)
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0xCE02-0x10000
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0x46
   stb %r3,0(%r7)
   bl record
   lha %r3,2(%r4)
   cmpdi %r3,0x4600
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0x8A
   stb %r3,1(%r7)
   bl record
   lha %r3,2(%r4)
   cmpdi %r3,0x468A
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stbx
0: addi %r7,%r4,2
   mr %r0,%r7
   li %r11,-2
   li %r3,0xDF
   stbx %r3,%r7,%r11
   bl record
   li %r3,0
   lbz %r3,0(%r4)
   cmpdi %r3,0xDF
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,1
   li %r3,0xDE
   stbx %r3,0,%r4
   bl record
   li %r3,0
   lbz %r3,0(%r4)
   cmpdi %r3,0xDE
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # stbu
0: addi %r7,%r4,2
   li %r3,0xCE
   stbu %r3,-2(%r7)
   bl record
   li %r3,0
   lbz %r3,0(%r4)
   cmpdi %r3,0xCE
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stbux
0: addi %r7,%r4,2
   li %r11,-2
   li %r3,0xDF
   stbux %r3,%r7,%r11
   bl record
   li %r3,0
   lbz %r3,0(%r4)
   cmpdi %r3,0xDF
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # sth
0: li %r3,0
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   addi %r7,%r4,2
   mr %r0,%r7
   li %r3,0x1234
   sth %r3,-2(%r7)
   bl record
   lwz %r3,0(%r4)
   lis %r11,0x1234
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r3,0x5678
   sth %r3,0(%r7)
   bl record
   lwz %r3,0(%r4)
   lis %r11,0x1234
   addi %r11,%r11,0x5678
   cmpd %r3,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # sthx
0: addi %r7,%r4,2
   mr %r0,%r7
   li %r11,-2
   li %r3,0x4321
   sthx %r3,%r7,%r11
   bl record
   li %r3,0
   lha %r3,0(%r4)
   cmpdi %r3,0x4321
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,2
   li %r3,0x3214
   sthx %r3,0,%r4
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x3214
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # sthu
0: addi %r7,%r4,2
   li %r3,0x1234
   sthu %r3,-2(%r7)
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x1234
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # sthux
0: addi %r7,%r4,2
   li %r11,-2
   li %r3,0x4321
   sthux %r3,%r7,%r11
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x4321
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stw was tested in the bootstrap code.

   # stwx
0: li %r3,0
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   addi %r7,%r4,4
   mr %r0,%r7
   li %r11,-4
   lis %r3,0x0123
   addi %r3,%r3,0x4567
   stwx %r3,%r7,%r11
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x0123
   bne 1f
   lha %r3,2(%r4)
   cmpdi %r3,0x4567
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,4
   lis %r3,0x7654
   addi %r3,%r3,0x3210
   stwx %r3,0,%r4
   bl record
   lha %r3,0(%r4)
   lha %r8,2(%r4)
   cmpdi %r3,0x7654
   bne 1f
   cmpdi %r8,0x3210
   beq 0f
1: sth %r3,12(%r6)
   sth %r8,14(%r6)
   addi %r6,%r6,32

   # stwu
0: addi %r7,%r4,4
   lis %r3,0x1234
   addi %r3,%r3,0x5678
   stwu %r3,-4(%r7)
   bl record
   lha %r3,0(%r4)
   lha %r8,2(%r4)
   cmpdi %r3,0x1234
   bne 1f
   cmpdi %r8,0x5678
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: sth %r3,12(%r6)
   sth %r8,14(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stwux
0: addi %r7,%r4,4
   li %r11,-4
   lis %r3,0x7654
   addi %r3,%r3,0x3210
   stwux %r3,%r7,%r11
   bl record
   lha %r3,0(%r4)
   lha %r8,2(%r4)
   cmpdi %r3,0x7654
   bne 1f
   cmpdi %r8,0x3210
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: sth %r3,12(%r6)
   sth %r8,14(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # std
0: li %r3,0
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   addi %r7,%r4,4
   mr %r0,%r7
   lis %r3,0x0112
   addi %r3,%r3,0x2334
   li %r11,32
   sld %r3,%r3,%r11
   addis %r3,%r3,0x4556
   addi %r3,%r3,0x6778
   std %r3,-4(%r7)
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0112
   addi %r11,%r11,0x2334
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x4556
   addi %r11,%r11,0x6778
   cmpd %r8,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: lis %r3,0x0123
   addi %r3,%r3,0x4567
   li %r11,32
   sld %r3,%r3,%r11
   addis %r3,%r3,0x7654
   addi %r3,%r3,0x3210
   std %r3,0(%r4)
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0123
   addi %r11,%r11,0x4567
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x7654
   addi %r11,%r11,0x3210
   cmpd %r8,%r11
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stdx
0: addi %r7,%r4,4
   mr %r0,%r7
   li %r11,-4
   lis %r3,0x0112
   addi %r3,%r3,0x2334
   li %r8,32
   sld %r3,%r3,%r8
   addis %r3,%r3,0x4556
   addi %r3,%r3,0x6778
   stdx %r3,%r7,%r11
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0112
   addi %r11,%r11,0x2334
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x4556
   addi %r11,%r11,0x6778
   cmpd %r8,%r11
   bne 1f
   cmpd %r7,%r0
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,2
   lis %r3,0x0123
   addi %r3,%r3,0x4567
   li %r11,32
   sld %r3,%r3,%r11
   addis %r3,%r3,0x7654
   addi %r3,%r3,0x3210
   stdx %r3,0,%r4
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0123
   addi %r11,%r11,0x4567
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x7654
   addi %r11,%r11,0x3210
   cmpd %r8,%r11
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stdu
0: addi %r7,%r4,4
   lis %r3,0x0112
   addi %r3,%r3,0x2334
   li %r11,32
   sld %r3,%r3,%r11
   addis %r3,%r3,0x4556
   addi %r3,%r3,0x6778
   stdu %r3,-4(%r7)
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0112
   addi %r11,%r11,0x2334
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x4556
   addi %r11,%r11,0x6778
   cmpd %r8,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stdux
0: addi %r7,%r4,4
   li %r11,-4
   lis %r3,0x0123
   addi %r3,%r3,0x4567
   li %r8,32
   sld %r3,%r3,%r8
   addis %r3,%r3,0x7654
   addi %r3,%r3,0x3210
   stdux %r3,%r7,%r11
   bl record
   lwa %r3,0(%r4)
   lwa %r8,4(%r4)
   lis %r11,0x0123
   addi %r11,%r11,0x4567
   cmpd %r3,%r11
   bne 1f
   lis %r11,0x7654
   addi %r11,%r11,0x3210
   cmpd %r8,%r11
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.4 Fixed-Point Load and Store with Byte Reversal Instructions
   ########################################################################

   # lhbrx
0: li %r3,0
   stw %r3,4(%r4)
   addi %r7,%r4,4
   li %r11,-4
   li %r3,0x1234
   sth %r3,0(%r4)
   lhbrx %r3,%r7,%r11
   bl record
   cmpdi %r3,0x3412
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,4
   lhbrx %r3,0,%r4
   bl record
   cmpdi %r3,0x3412
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # lwbrx
0: lis %r3,0x0123
   addi %r3,%r3,0x4567
   stw %r3,0(%r4)
   lwbrx %r3,%r7,%r11
   bl record
   lis %r11,0x6745
   addi %r11,%r11,0x2301
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,4
   lwbrx %r3,0,%r4
   bl record
   lis %r11,0x6745
   addi %r11,%r11,0x2301
   cmpd %r3,%r11
   beq 0f

   # sthbrx
0: addi %r7,%r4,4
   li %r11,-4
   li %r3,0x1234
   sthbrx %r3,%r7,%r11
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x3412
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,4
   li %r3,0x5678
   sthbrx %r3,0,%r4
   bl record
   lha %r3,0(%r4)
   cmpdi %r3,0x7856
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # stwbrx
0: addi %r7,%r4,4
   li %r11,-4
   lis %r3,0x0123
   addi %r3,%r3,0x4567
   stwbrx %r3,%r7,%r11
   bl record
   lwz %r3,0(%r4)
   lis %r11,0x6745
   addi %r11,%r11,0x2301
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,4
   lis %r3,0x7654
   addi %r3,%r3,0x3210
   stwbrx %r3,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r11,0x1032
   addi %r11,%r11,0x5476
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.5 Fixed-Point Load and Store Multiple Instructions
   ########################################################################

0: li %r3,-1
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   stw %r3,8(%r4)
   stw %r3,12(%r4)
   stw %r3,16(%r4)
   stw %r3,20(%r4)
   stw %r3,24(%r4)
   stw %r3,28(%r4)
   stw %r3,32(%r4)
   stw %r3,252(%r4)
   stw %r3,256(%r4)
   stw %r3,260(%r4)

   # stmw
   li %r24,24
   li %r25,25
   li %r26,26
   li %r27,27
   li %r28,28
   li %r29,29
   li %r30,30
   li %r31,31
   addi %r7,%r4,4
   stmw %r24,-4(%r7)
   bl record
   lwz %r3,0(%r4)
   li %r7,24
   cmpdi %r3,24
   bne 1f
   lwz %r3,4(%r4)
   li %r7,25
   cmpdi %r3,25
   bne 1f
   lwz %r3,8(%r4)
   li %r7,26
   cmpdi %r3,26
   bne 1f
   lwz %r3,12(%r4)
   li %r7,27
   cmpdi %r3,27
   bne 1f
   lwz %r3,16(%r4)
   li %r7,28
   cmpdi %r3,28
   bne 1f
   lwz %r3,20(%r4)
   li %r7,29
   cmpdi %r3,29
   bne 1f
   lwz %r3,24(%r4)
   li %r7,30
   cmpdi %r3,30
   bne 1f
   lwz %r3,28(%r4)
   li %r7,31
   cmpdi %r3,31
   bne 1f
   lwa %r3,32(%r4)
   li %r7,32
   cmpdi %r3,-1
   beq 0f
1: stw %r3,8(%r6)
   stw %r7,12(%r6)
   addi %r6,%r6,32

0: li %r30,300
   li %r31,310
   addi %r7,%r4,-0x7F00
   stmw %r30,0x7FFC(%r7)  # Offset should not wrap around to -0x8000.
   bl record
   lwz %r3,252(%r4)
   li %r7,30
   cmpdi %r3,300
   bne 1f
   lwz %r3,256(%r4)
   li %r7,31
   cmpdi %r3,310
   bne 1f
   lwa %r3,260(%r4)
   li %r7,32
   cmpdi %r3,-1
   beq 0f
1: stw %r3,8(%r6)
   stw %r7,12(%r6)
   addi %r6,%r6,32

   # lmw
0: li %r24,-2
   li %r25,-2
   li %r26,-2
   li %r27,-2
   li %r28,-2
   li %r29,-2
   li %r30,-2
   li %r31,-2
   addi %r7,%r4,4
   lmw %r24,-4(%r7)
   bl record
   mr %r3,%r24
   li %r7,24
   cmpdi %r3,24
   bne 1f
   mr %r3,%r25
   li %r7,25
   cmpdi %r3,25
   bne 1f
   mr %r3,%r26
   li %r7,26
   cmpdi %r3,26
   bne 1f
   mr %r3,%r27
   li %r7,27
   cmpdi %r3,27
   bne 1f
   mr %r3,%r28
   li %r7,28
   cmpdi %r3,28
   bne 1f
   mr %r3,%r29
   li %r7,29
   cmpdi %r3,29
   bne 1f
   mr %r3,%r30
   li %r7,30
   cmpdi %r3,30
   bne 1f
   mr %r3,%r31
   li %r7,31
   cmpdi %r3,31
   beq 0f
1: stw %r3,8(%r6)
   stw %r7,12(%r6)
   addi %r6,%r6,32

0: li %r30,-2
   li %r31,-2
   addi %r7,%r4,-0x7F00
   lmw %r30,0x7FFC(%r7)  # Offset should not wrap around to -0x8000.
   bl record
   mr %r3,%r30
   li %r7,30
   cmpdi %r3,300
   bne 1f
   mr %r3,%r31
   li %r7,31
   cmpdi %r3,310
   beq 0f
1: stw %r3,8(%r6)
   stw %r7,12(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.6 Fixed-Point Move Assist Instructions
   # 3.3.13 Move To/From System Register Instructions - mtxer
   ########################################################################

0: li %r3,0
   li %r0,256
   mtctr %r0
1: stbx %r3,%r4,%r3
   addi %r3,%r3,1
   bdnz 1b

   # lswi (NB!=0, no register wrap)
0: addi %r7,%r4,1
   lswi %r24,%r7,9
   bl record
   lis %r3,0x0102
   addi %r3,%r3,0x0304
   cmpd %r24,%r3
   bne 1f
   lis %r3,0x0506
   addi %r3,%r3,0x0708
   cmpd %r25,%r3
   bne 1f
   lis %r3,0x0900
   cmpd %r26,%r3
   beq 0f
1: std %r24,8(%r6)
   std %r25,16(%r6)
   std %r26,24(%r6)
   addi %r6,%r6,32

   # lswi (NB==0, register wrap)
0: addi %r7,%r4,18
   lswi %r25,%r7,32
   bl record
   lis %r3,0x1213
   addi %r3,%r3,0x1415
   cmpd %r25,%r3
   bne 1f
   lis %r3,0x1617
   addi %r3,%r3,0x1819
   cmpd %r26,%r3
   bne 1f
   lis %r3,0x1A1B
   addi %r3,%r3,0x1C1D
   cmpd %r27,%r3
   bne 1f
   lis %r3,0x1E1F
   addi %r3,%r3,0x2021
   cmpd %r28,%r3
   bne 1f
   lis %r3,0x2223
   addi %r3,%r3,0x2425
   cmpd %r29,%r3
   bne 1f
   lis %r3,0x2627
   addi %r3,%r3,0x2829
   cmpd %r30,%r3
   bne 1f
   lis %r3,0x2A2B
   addi %r3,%r3,0x2C2D
   cmpd %r31,%r3
   bne 1f
   lis %r3,0x2E2F
   addi %r3,%r3,0x3031
   cmpd %r0,%r3
   beq 0f
1: std %r24,8(%r6)
   std %r31,16(%r6)
   std %r0,24(%r6)
   addi %r6,%r6,32

   # lswx (RA!=0, register wrap)
0: li %r3,9
   mtxer %r3
   li %r7,1
   lswx %r30,%r4,%r7
   bl record
   lis %r3,0x0102
   addi %r3,%r3,0x0304
   cmpd %r30,%r3
   bne 1f
   lis %r3,0x0506
   addi %r3,%r3,0x0708
   cmpd %r31,%r3
   bne 1f
   lis %r3,0x0900
   cmpd %r0,%r3
   beq 0f
1: std %r30,8(%r6)
   std %r31,16(%r6)
   std %r0,24(%r6)
   addi %r6,%r6,32

   # lswx (RA==0, no register wrap)
0: li %r3,11
   mtxer %r3
   addi %r7,%r4,8
   li %r0,2
   lswx %r26,%r0,%r7
   bl record
   lis %r3,0x0809
   addi %r3,%r3,0x0A0B
   cmpd %r26,%r3
   bne 1f
   lis %r3,0x0C0D
   addi %r3,%r3,0x0E0F
   cmpd %r27,%r3
   bne 1f
   lis %r3,0x1011
   addi %r3,%r3,0x1200
   cmpd %r28,%r3
   beq 0f
1: std %r26,8(%r6)
   std %r27,16(%r6)
   std %r28,24(%r6)
   addi %r6,%r6,32

   # lswx (count==0)
0: li %r25,-1
   li %r3,0
   mtxer %r3
   lswx %r24,%r0,%r4
   bl record
   cmpdi %r25,-1
   beq 0f
   std %r25,8(%r6)
   addi %r6,%r6,32

0: lis %r24,0x5051
   addi %r24,%r24,0x5253
   lis %r25,0x5455
   addi %r25,%r25,0x5657
   lis %r26,0x5859
   addi %r26,%r26,0x5A5B
   lis %r27,0x5C5D
   addi %r27,%r27,0x5E5F
   lis %r28,0x6061
   addi %r28,%r28,0x6263
   lis %r29,0x6465
   addi %r29,%r29,0x6667
   lis %r30,0x6869
   addi %r30,%r30,0x6A6B
   lis %r31,0x6C6D
   addi %r31,%r31,0x6E6F
   lis %r3,0x7071
   addi %r3,%r3,0x7273
   mr %r0,%r3

   # stswi (NB!=0, no register wrap)
0: addi %r7,%r4,1
   stswi %r24,%r7,9
   bl record
   lbz %r3,1(%r4)
   lhz %r8,2(%r4)
   lhz %r9,4(%r4)
   lhz %r10,6(%r4)
   lhz %r11,8(%r4)
   cmpdi %r3,0x50
   bne 1f
   cmpdi %r8,0x5152
   bne 1f
   cmpdi %r9,0x5354
   bne 1f
   cmpdi %r10,0x5556
   bne 1f
   cmpdi %r11,0x5758
   beq 0f
1: sth %r3,8(%r6)
   sth %r8,10(%r6)
   sth %r9,12(%r6)
   sth %r10,14(%r6)
   sth %r11,16(%r6)
   addi %r6,%r6,32

   # stswi (NB==0, register wrap)
0: addi %r7,%r4,18
   stswi %r25,%r7,32
   bl record
   lhz %r3,18(%r4)
   cmpdi %r3,0x5455
   bne 1f
   lhz %r3,20(%r4)
   cmpdi %r3,0x5657
   bne 1f
   lhz %r3,22(%r4)
   cmpdi %r3,0x5859
   bne 1f
   lhz %r3,24(%r4)
   cmpdi %r3,0x5A5B
   bne 1f
   lhz %r3,26(%r4)
   cmpdi %r3,0x5C5D
   bne 1f
   lhz %r3,28(%r4)
   cmpdi %r3,0x5E5F
   bne 1f
   lhz %r3,30(%r4)
   cmpdi %r3,0x6061
   bne 1f
   lhz %r3,32(%r4)
   cmpdi %r3,0x6263
   bne 1f
   lhz %r3,34(%r4)
   cmpdi %r3,0x6465
   bne 1f
   lhz %r3,36(%r4)
   cmpdi %r3,0x6667
   bne 1f
   lhz %r3,38(%r4)
   cmpdi %r3,0x6869
   bne 1f
   lhz %r3,40(%r4)
   cmpdi %r3,0x6A6B
   bne 1f
   lhz %r3,42(%r4)
   cmpdi %r3,0x6C6D
   bne 1f
   lhz %r3,44(%r4)
   cmpdi %r3,0x6E6F
   bne 1f
   lhz %r3,46(%r4)
   cmpdi %r3,0x7071
   bne 1f
   lhz %r3,48(%r4)
   cmpdi %r3,0x7273
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

   # stswx (RA!=0, register wrap)
0: li %r3,9
   mtxer %r3
   li %r7,1
   stswx %r30,%r4,%r7
   bl record
   lbz %r3,1(%r4)
   lhz %r8,2(%r4)
   lhz %r9,4(%r4)
   lhz %r10,6(%r4)
   lhz %r11,8(%r4)
   cmpdi %r3,0x68
   bne 1f
   cmpdi %r8,0x696A
   bne 1f
   cmpdi %r9,0x6B6C
   bne 1f
   cmpdi %r10,0x6D6E
   bne 1f
   cmpdi %r11,0x6F70
   beq 0f
1: sth %r3,8(%r6)
   sth %r8,10(%r6)
   sth %r9,12(%r6)
   sth %r10,14(%r6)
   sth %r11,16(%r6)
   addi %r6,%r6,32

   # stswx (RA==0, no register wrap)
0: li %r3,11
   mtxer %r3
   addi %r7,%r4,8
   li %r0,2
   stswx %r26,%r0,%r7
   bl record
   lhz %r3,8(%r4)
   cmpdi %r3,0x5859
   bne 1f
   lhz %r3,10(%r4)
   cmpdi %r3,0x5A5B
   bne 1f
   lhz %r3,12(%r4)
   cmpdi %r3,0x5C5D
   bne 1f
   lhz %r3,14(%r4)
   cmpdi %r3,0x5E5F
   bne 1f
   lhz %r3,16(%r4)
   cmpdi %r3,0x6061
   bne 1f
   lbz %r3,18(%r4)
   cmpdi %r3,0x62
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

   # stswx (count==0)
0: li %r24,-1
   li %r3,0
   mtxer %r3
   li %r3,-2
   stb %r3,0(%r4)
   stswx %r24,%r0,%r4
   bl record
   lbz %r3,0(%r4)
   cmpdi %r3,0xFE
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.13 Move To/From System Register Instructions - mfxer, mtxer
   ########################################################################

   # mfxer
0: li %r3,0x12
   mtxer %r3
   li %r3,-1
   addic. %r3,%r3,1
   mfxer %r3
   bl record
   lis %r7,0x2000
   addi %r7,%r7,0x12
   cmpd %r3,%r7
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtxer (check that it overwrites the CA bit)
0: li %r3,0x34
   mtxer %r3
   bl record
   li %r3,0
   mfxer %r3
   cmpdi %r3,0x34
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - addi, addis, add, subf
   ########################################################################

0: li %r3,0
   mtxer %r3
   mtcr %r3
   li %r31,32       # For shifts.

   # addi and addis were tested in the bootstrap code.

   # add
0: li %r8,-4
   li %r9,9
   add %r3,%r8,%r9
   bl record
   li %r7,5
   bl check_alu

   # add.
0: li %r8,-4
   li %r9,3
   add. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,1
   add. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,1
   add. %r3,%r3,%r9
   bl record
   li %r7,1
   bl check_alu_gt

   # addo
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addo %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addo %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov
   # Also check that SO is preserved even when OV is cleared.
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addo %r3,%r8,%r9
   addo %r3,%r9,%r3
   addo %r3,%r9,%r3
   bl record
   lis %r7,0xD000
   sld %r7,%r7,%r31
   bl check_alu_so

   # addo.
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addo. %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu_gt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addo. %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   addo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addo. %r3,%r8,%r9
   addo. %r3,%r9,%r3
   addo. %r3,%r9,%r3
   bl record
   lis %r7,0xD000
   sld %r7,%r7,%r31
   bl check_alu_so_lt

   # subf
0: li %r8,4
   li %r9,9
   subf %r3,%r8,%r9
   bl record
   li %r7,5
   bl check_alu

   # subf.
0: li %r8,4
   li %r9,3
   subf. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,-1
   subf. %r3,%r8,%r3
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-1
   subf. %r3,%r9,%r3
   bl record
   li %r7,1
   bl check_alu_gt

   # subfo
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfo %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfo %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   bl check_alu_ov
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfo %r3,%r9,%r8
   subfo %r3,%r9,%r3
   subfo %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   bl check_alu_so
   # Check that overflow from the +1 in ~(RA)+(RB)+1 is detected.
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x4000
   sld %r9,%r9,%r31
   subfo %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # subfo.
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfo. %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   bl check_alu_lt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfo. %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   bl check_alu_ov_gt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   subfo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfo. %r3,%r9,%r8
   subfo. %r3,%r9,%r3
   subfo. %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   bl check_alu_so_gt
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x4000
   sld %r9,%r9,%r31
   subfo. %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - addic, addic., subfic, addc, subfc
   ########################################################################

   # addic
   # Use r0 here to verify that it doesn't get treated as zero like addi/addis.
0: li %r0,1
   addic %r3,%r0,2
   bl record
   li %r7,3
   bl check_alu
0: li %r0,-1
   addic %r3,%r0,3
   bl record
   li %r7,2
   bl check_alu_ca
   # XER[CA] should not be an input to the add.
0: li %r0,-1
   addic %r3,%r0,3
   addic %r3,%r3,0
   bl record
   li %r7,2
   bl check_alu

   # addic.
0: li %r0,-3
   addic. %r3,%r0,1
   bl record
   li %r7,-2
   bl check_alu_lt
0: addic. %r3,%r3,2
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r0,-1
   addic. %r3,%r0,3
   addic. %r3,%r3,0
   bl record
   li %r7,2
   bl check_alu_gt

   # subfic
0: li %r0,2
   subfic %r3,%r0,1
   bl record
   li %r7,-1
   bl check_alu
0: li %r0,1
   subfic %r3,%r0,1
   bl record
   li %r7,0
   bl check_alu_ca

   # addc
0: li %r8,-4
   li %r9,3
   addc %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu
0: li %r8,2
   addc %r3,%r3,%r8
   bl record
   li %r7,1
   bl check_alu_ca

   # addc.
0: li %r8,-4
   li %r9,3
   addc. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,1
   addc. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r9,1
   addc. %r3,%r3,%r9
   bl record
   li %r7,1
   bl check_alu_gt

   # addco
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addco %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addco %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov
0: lis %r9,0x7000
   sld %r9,%r9,%r31
   addco %r3,%r3,%r9
   bl record
   lis %r7,0x1000
   sld %r7,%r7,%r31
   bl check_alu_ca
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x6000
   sld %r9,%r9,%r31
   addco %r3,%r8,%r9
   addco %r3,%r9,%r3
   bl record
   li %r7,0
   bl check_alu_ca_so

   # addco.
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addco. %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu_gt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addco. %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   addco. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r8,0x5000
   sld %r8,%r8,%r31
   lis %r9,0x6000
   sld %r9,%r9,%r31
   addco. %r3,%r8,%r9
   addco. %r3,%r9,%r3
   bl record
   lis %r7,0x1000
   sld %r7,%r7,%r31
   bl check_alu_ca_so_gt

   # subfc
0: li %r8,4
   li %r9,9
   subfc %r3,%r8,%r9
   bl record
   li %r7,5
   bl check_alu_ca
0: li %r8,4
   li %r9,9
   subfc %r3,%r9,%r8
   bl record
   li %r7,-5
   bl check_alu

   # subfc.
0: li %r8,4
   li %r9,3
   subfc. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,-1
   subfc. %r3,%r8,%r3
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r9,-1
   subfc. %r3,%r9,%r3
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r9,3
   subfc. %r3,%r3,%r9
   bl record
   li %r7,2
   bl check_alu_ca_gt

   # subfco
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfco %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   bl check_alu_ca
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfco %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   bl check_alu_ca_ov
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfco %r3,%r9,%r8
   subfco %r3,%r9,%r3
   subfco %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   bl check_alu_ca_so
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x4000
   sld %r9,%r9,%r31
   subfco %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # subfco.
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfco. %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   bl check_alu_ca_lt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfco. %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   bl check_alu_ca_ov_gt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   subfco. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfco. %r3,%r9,%r8
   subfco. %r3,%r9,%r3
   subfco. %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   bl check_alu_ca_so_gt
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x4000
   sld %r9,%r9,%r31
   subfco. %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - adde, subfe
   ########################################################################

   # adde
0: li %r8,-4
   li %r9,3
   adde %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu
0: li %r8,2
   adde %r3,%r3,%r8
   bl record
   li %r7,1
   bl check_alu_ca
   # Check that the carry bit is added and carry resulting from adding the
   # carry bit is detected.
0: li %r3,-1
   li %r8,2
   adde %r3,%r8,%r3
   li %r9,-2
   adde %r3,%r9,%r3
   bl record
   li %r7,0
   bl check_alu_ca

   # adde.
0: li %r8,-4
   li %r9,3
   adde. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,1
   adde. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r9,1
   adde. %r3,%r3,%r9
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r3,-1
   li %r8,2
   adde. %r3,%r8,%r3
   li %r9,-2
   adde. %r3,%r9,%r3
   bl record
   li %r7,0
   bl check_alu_ca_eq

   # addeo
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addeo %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addeo %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov
0: lis %r9,0x7000
   sld %r9,%r9,%r31
   addeo %r3,%r3,%r9
   bl record
   lis %r7,0x1000
   sld %r7,%r7,%r31
   bl check_alu_ca
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0xA000
   sld %r9,%r9,%r31
   addeo %r3,%r8,%r9
   addi %r9,%r9,-1
   addeo %r3,%r9,%r3
   bl record
   li %r7,0
   bl check_alu_ca_so

   # addeo.
0: lis %r8,0x4000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   addeo. %r3,%r8,%r9
   bl record
   lis %r7,0x7000
   sld %r7,%r7,%r31
   bl check_alu_gt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   addeo. %r3,%r3,%r8
   bl record
   lis %r7,0xA000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   addeo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0xA000
   sld %r9,%r9,%r31
   addeo. %r3,%r8,%r9
   addi %r9,%r9,-1
   addeo. %r3,%r9,%r3
   bl record
   li %r7,0
   bl check_alu_ca_so_eq

   # subfe
0: li %r8,4
   li %r9,9
   subfe %r3,%r8,%r9
   bl record
   li %r7,4
   bl check_alu_ca
0: li %r8,4
   li %r9,9
   subfe %r3,%r9,%r8
   bl record
   li %r7,-6
   bl check_alu
0: li %r8,4
   li %r9,9
   subfe %r3,%r8,%r9
   subfe %r3,%r8,%r3
   bl record
   li %r7,0
   bl check_alu_ca

   # subfe.
0: li %r8,3
   li %r9,3
   subfe. %r3,%r8,%r9
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,-2
   subfe. %r3,%r8,%r3
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r9,-2
   subfe. %r3,%r9,%r3
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r9,4
   subfe. %r3,%r3,%r9
   bl record
   li %r7,2
   bl check_alu_ca_gt
0: li %r9,4
   subfe. %r3,%r3,%r9
   li %r8,1
   subfe. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_ca_eq

   # subfeo
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfeo %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfeo %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   addi %r7,%r7,-2
   bl check_alu_ca_ov
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfeo %r3,%r9,%r8
   subfeo %r3,%r9,%r3
   subfeo %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_so
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x8000
   sld %r9,%r9,%r31
   addi %r9,%r9,-1
   subfeo %r9,%r9,%r8
   subfeo %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # subfeo.
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfeo. %r3,%r9,%r8
   bl record
   lis %r7,0x9000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_lt
0: lis %r8,0x3000
   sld %r8,%r8,%r31
   subfeo. %r3,%r8,%r3
   bl record
   lis %r7,0x6000
   sld %r7,%r7,%r31
   addi %r7,%r7,-2
   bl check_alu_ca_ov_gt
0: lis %r9,0x6000
   sld %r9,%r9,%r31
   addi %r9,%r9,-1
   subfeo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x3000
   sld %r9,%r9,%r31
   subfeo. %r3,%r9,%r8
   subfeo. %r3,%r9,%r3
   subfeo. %r3,%r9,%r3
   bl record
   lis %r7,0x3000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_so_gt
0: lis %r8,0xC000
   sld %r8,%r8,%r31
   lis %r9,0x8000
   sld %r9,%r9,%r31
   addi %r9,%r9,-1
   subfeo %r9,%r9,%r8
   subfeo. %r7,%r8,%r9
   bl record
   mr %r3,%r7
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - addme, subfme
   ########################################################################

   # addme
0: li %r8,0
   addme %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,1
   addme %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: li %r9,1
   addme %r3,%r9
   addme %r3,%r3
   bl record
   li %r7,0
   bl check_alu_ca

   # addme.
0: li %r8,0
   addme. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,1
   addme. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r7,2
   addme. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_ca_gt

   # addmeo
0: li %r8,0
   addmeo %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,1
   addmeo %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   addmeo %r3,%r7
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_ov

   # addmeo.
0: li %r8,0
   addmeo. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,1
   addmeo. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r7,2
   addmeo. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_ca_gt
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   addmeo. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_ov_gt

   # subfme
0: li %r8,-1
   subfme %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,-2
   subfme %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: li %r9,-2
   subfme %r3,%r9
   li %r3,-1
   subfme %r3,%r3
   bl record
   li %r7,0
   bl check_alu_ca

   # subfme.
0: li %r8,-1
   subfme. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-2
   subfme. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r7,-3
   subfme. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_ca_gt

   # subfmeo
0: li %r8,-1
   subfmeo %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,-2
   subfmeo %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   subfmeo %r3,%r7
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_ov

   # subfmeo.
0: li %r8,-1
   subfmeo. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-2
   subfmeo. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: li %r7,-3
   subfmeo. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_ca_gt
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   addi %r3,%r3,-1
   subfmeo. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   bl check_alu_ca_ov_gt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - addze, subfze
   ########################################################################

   # addze
0: li %r8,1
   addze %r3,%r8
   bl record
   li %r7,1
   bl check_alu
   # addze and subfze can never cause a carry without an incoming carry bit.
0: lis %r0,0x2000
   mtxer %r0
   li %r9,-1
   addze %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca

   # addze.
0: li %r8,-1
   addze. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,0
   addze. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r7,1
   addze. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: lis %r0,0x2000
   mtxer %r0
   li %r9,-1
   addze. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq

   # addzeo
0: li %r8,1
   addzeo %r3,%r8
   bl record
   li %r7,1
   bl check_alu
0: lis %r0,0x2000
   mtxer %r0
   li %r9,-1
   addze %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: lis %r0,0x2000
   mtxer %r0
   lis %r7,0x8000
   sld %r7,%r7,%r31
   addi %r7,%r7,-1
   addzeo %r3,%r7
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # addzeo.
0: li %r8,-1
   addzeo. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,0
   addzeo. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r7,1
   addzeo. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: lis %r0,0x2000
   mtxer %r0
   li %r0,-1
   addze. %r3,%r0
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r0,0x2000
   mtxer %r0
   lis %r3,0x8000
   sld %r3,%r3,%r31
   addi %r3,%r3,-1
   addzeo. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   # subfze
0: li %r8,-2
   subfze %r3,%r8
   bl record
   li %r7,1
   bl check_alu
0: lis %r0,0x2000
   mtxer %r0
   li %r9,0
   subfze %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca

   # subfze.
0: li %r8,0
   subfze. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-1
   subfze. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r7,-2
   subfze. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: lis %r0,0x2000
   mtxer %r0
   li %r9,0
   subfze. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca_eq

   # subfzeo
0: li %r8,-2
   subfzeo %r3,%r8
   bl record
   li %r7,1
   bl check_alu
0: lis %r0,0x2000
   mtxer %r0
   li %r9,0
   subfze %r3,%r9
   bl record
   li %r7,0
   bl check_alu_ca
0: lis %r0,0x2000
   mtxer %r0
   lis %r7,0x8000
   sld %r7,%r7,%r31
   subfzeo %r3,%r7
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # subfzeo.
0: li %r8,0
   subfzeo. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-1
   subfzeo. %r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r7,-2
   subfzeo. %r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: lis %r0,0x2000
   mtxer %r0
   li %r0,0
   subfze. %r3,%r0
   bl record
   li %r7,0
   bl check_alu_ca_eq
0: lis %r0,0x2000
   mtxer %r0
   lis %r3,0x8000
   sld %r3,%r3,%r31
   subfzeo. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - neg
   ########################################################################

   # neg
0: li %r8,1
   neg %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,-2
   neg %r3,%r9
   bl record
   li %r7,2
   bl check_alu
0: li %r7,0
   neg %r3,%r7
   bl record
   li %r7,0
   bl check_alu
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   neg %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu

   # neg.
0: li %r8,1
   neg. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-2
   neg. %r3,%r9
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r7,0
   neg. %r3,%r7
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   neg. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_lt

   # nego
0: li %r8,1
   nego %r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: li %r9,-2
   nego %r3,%r9
   bl record
   li %r7,2
   bl check_alu
0: li %r7,0
   nego %r3,%r7
   bl record
   li %r7,0
   bl check_alu
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   nego %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov

   # nego.
0: li %r8,1
   nego. %r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r9,-2
   nego. %r3,%r9
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r7,0
   nego. %r3,%r7
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r3,0x8000
   sld %r3,%r3,%r31
   nego. %r3,%r3
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - mulli
   ########################################################################

   # mulli
0: li %r8,3
   mulli %r3,%r8,5
   bl record
   li %r7,15
   bl check_alu
0: mulli %r3,%r3,-7
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x10
   sld %r8,%r8,%r31
   addi %r8,%r8,1
   mulli %r3,%r8,0x1111
   bl record
   lis %r7,0x1110
   sld %r7,%r7,%r31
   addi %r7,%r7,0x1111
   bl check_alu

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - mulld, mullw
   ########################################################################

   # mulld
0: li %r8,3
   li %r9,5
   mulld %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: li %r8,-7
   mulld %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x10
   sld %r8,%r8,%r31
   addi %r8,%r8,1
   li %r7,0x1111
   mulld %r3,%r8,%r7
   bl record
   lis %r7,0x1110
   sld %r7,%r7,%r31
   addi %r7,%r7,0x1111
   bl check_alu

   # mulld.
0: li %r8,3
   li %r9,5
   mulld. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,-7
   mulld. %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r9,0
   mulld. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq

   # mulldo
0: li %r8,3
   li %r9,5
   mulldo %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: li %r8,-7
   mulldo %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x10
   sld %r8,%r8,%r31
   addi %r8,%r8,1
   li %r7,0x1111
   mulldo %r3,%r8,%r7
   bl record
   lis %r7,0x1110
   sld %r7,%r7,%r31
   addi %r7,%r7,0x1111
   bl check_alu_ov

   # mulldo.
0: li %r8,3
   li %r9,5
   mulldo. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,-7
   mulldo. %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r9,0
   mulldo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0x10
   sld %r8,%r8,%r31
   addi %r8,%r8,1
   li %r7,0x1111
   mulldo. %r3,%r8,%r7
   bl record
   lis %r7,0x1110
   sld %r7,%r7,%r31
   addi %r7,%r7,0x1111
   bl check_alu_ov_gt

   # mullw
0: li %r8,3
   li %r9,5
   mullw %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
   # Use 0x0000_0000_FFFF_xxxx to verify that operand is interpreted as int32.
0: li %r8,1
   sld %r8,%r8,%r31
   addi %r8,%r8,-7
   mullw %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x10
   addi %r8,%r8,1
   li %r7,0x1111
   mullw %r3,%r8,%r7
   bl record
   li %r0,20
   sld %r7,%r7,%r0
   addi %r7,%r7,0x1111
   bl check_alu

   # mullw.
0: li %r8,3
   li %r9,5
   mullw. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,1
   sld %r8,%r8,%r31
   addi %r8,%r8,-7
   mullw. %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r9,0
   mullw. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq

   # mullwo
0: li %r8,3
   li %r9,5
   mullwo %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: li %r8,1
   sld %r8,%r8,%r31
   addi %r8,%r8,-7
   mullwo %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x10
   addi %r8,%r8,1
   li %r7,0x1111
   mullwo %r3,%r8,%r7
   bl record
   li %r0,20
   sld %r7,%r7,%r0
   addi %r7,%r7,0x1111
   bl check_alu_ov
0: lis %r8,0x10
   addi %r8,%r8,1
   li %r7,-0x1111
   mullwo %r3,%r7,%r8
   bl record
   li %r0,20
   sld %r7,%r7,%r0
   addi %r7,%r7,-0x1111
   bl check_alu_ov

   # mullwo.
0: li %r8,3
   li %r9,5
   mullwo. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,1
   sld %r8,%r8,%r31
   addi %r8,%r8,-7
   mullwo. %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r9,0
   mullwo. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0x10
   addi %r8,%r8,1
   li %r7,0x1111
   mullwo. %r3,%r8,%r7
   bl record
   li %r0,20
   sld %r7,%r7,%r0
   addi %r7,%r7,0x1111
   bl check_alu_ov_gt
0: lis %r8,0x10
   addi %r8,%r8,1
   li %r7,-0x1111
   mullwo. %r3,%r7,%r8
   bl record
   li %r0,20
   sld %r7,%r7,%r0
   addi %r7,%r7,-0x1111
   bl check_alu_ov_lt

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - mulhd, mulhw
   ########################################################################

   # mulhd
0: li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   mulhd %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: li %r8,-7
   mulhd %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu
0: lis %r8,0x1
   addi %r8,%r8,0x10
   sld %r8,%r8,%r31
   lis %r7,0x1111
   mulhd %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu
   # Check that the version of mulhd with the OE bit set doesn't affect XER
   # (OE is a reserved field in the mulh* instructions).  Note that a real
   # Cell processor raises an exception for mulh* instructions with both OE
   # and Rc set; those bit patterns are included below for reference,
   # bracketed by .if 0 / .endif so they are not actually executed.
# todo: fix this opcode
.if 0
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   .int 0x7C694492  # mulhd %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov
.endif
   # These tests compute 2^77+1 (0x0000_0000_0000_2000_0000_0000_0000_0001)
   # as 1417634610809 * 106597092297 with various signs, and they will fail
   # if 128-bit multiplication is not correctly implemented.
0: bl 2f
1: ld %r24,0(%r3)
   ld %r25,8(%r3)
   neg %r26,%r24
   neg %r27,%r25
   mulhd %r3,%r24,%r25
   bl record
   li %r7,0x2000
   bl check_alu
0: mulhd %r3,%r24,%r27
   bl record
   li %r7,-0x2001
   bl check_alu
0: mulhd %r3,%r26,%r25
   bl record
   li %r7,-0x2001
   bl check_alu
0: mulhd %r3,%r26,%r27
   bl record
   li %r7,0x2000
   bl check_alu
   b 0f
2: mflr %r3
   addi %r3,%r3,3f-1b
   blr
   .balign 8
3: .int 0x0000014A,0x119B7E79
   .int 0x00000018,0xD1AE8BC9

   # mulhd.
0: li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   mulhd. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,-7
   mulhd. %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu_lt
0: li %r8,3
   li %r9,5
   mulhd. %r3,%r9,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0x1
   addi %r8,%r8,0x10
   sld %r8,%r8,%r31
   lis %r7,0x1111
   mulhd. %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu_gt
.if 0  # mulhd. with OE=1 triggers an exception on the Cell, so we skip it.
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   .int 0x7C694493  # mulhd. %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov_gt
.endif

   # mulhw
0: lis %r8,3
   lis %r9,5
   mulhw %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: lis %r3,15
   li %r8,1
   sld %r8,%r8,%r31
   addis %r8,%r8,-7
   mulhw %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu
0: lis %r8,0x1
   addi %r8,%r8,0x10
   lis %r7,0x1111
   mulhw %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu
#todo: fix this opcode
.if 0
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   lis %r8,3
   lis %r9,5
   .int 0x7C694496  # mulhw %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov
.endif
   # mulhw.
0: lis %r8,3
   lis %r9,5
   mulhw. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   lis %r3,15
   li %r8,1
   sld %r8,%r8,%r31
   addis %r8,%r8,-7
   mulhw. %r3,%r3,%r8
   bl record
   li %r7,-105
   bl check_alu_so_undef
0: lis %r8,0x1
   addi %r8,%r8,0x10
   lis %r7,0x1111
   mulhw. %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu_undef
.if 0  # mulhw. with OE=1 triggers an exception on the Cell, so we skip it.
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   lis %r8,3
   lis %r9,5
   .int 0x7C694497  # mulhw. %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov_undef
.endif

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - mulhdu, mulhwu
   ########################################################################

   # mulhdu
0: li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   mulhdu %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: li %r8,-7
   mulhdu %r3,%r3,%r8
   bl record
   li %r7,14
   bl check_alu
0: lis %r8,0x1
   addi %r8,%r8,0x10
   sld %r8,%r8,%r31
   lis %r7,0x1111
   mulhdu %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu
#todo: fix this opcode
.if 0
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   .int 0x7C694412  # mulhdu %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov
.endif
   # mulhdu.
0: li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   mulhdu. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_gt
0: li %r8,-7
   mulhdu. %r3,%r3,%r8
   bl record
   li %r7,14
   bl check_alu_gt
0: li %r3,-15
   sld %r3,%r3,%r31
   li %r8,-7
   sld %r8,%r8,%r31
   mulhdu. %r3,%r8,%r3
   bl record
   li %r7,-22
   sld %r7,%r7,%r31
   addi %r7,%r7,105
   bl check_alu_lt
0: li %r8,3
   li %r9,5
   mulhdu. %r3,%r9,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r8,0x1
   addi %r8,%r8,0x10
   sld %r8,%r8,%r31
   lis %r7,0x1111
   mulhdu. %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu_gt
.if 0  # mulhdu. with OE=1 triggers an exception on the Cell, so we skip it.
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   li %r8,3
   sld %r8,%r8,%r31
   li %r9,5
   sld %r9,%r9,%r31
   .int 0x7C694413  # mulhdu. %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov_gt
.endif

   # mulhwu
0: lis %r8,3
   lis %r9,5
   mulhwu %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu
0: lis %r3,15
   li %r8,1
   sld %r8,%r8,%r31
   addis %r8,%r8,-7
   mulhwu %r3,%r3,%r8
   bl record
   lis %r7,15
   addi %r7,%r7,-105
   bl check_alu
0: lis %r8,0x1
   addi %r8,%r8,0x10
   lis %r7,0x1111
   mulhwu %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu
#todo: fix this opcode
.if 0
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   lis %r8,3
   lis %r9,5
   .int 0x7C694416  # mulhwu %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov
.endif
   # mulhwu.
0: lis %r8,3
   lis %r9,5
   mulhwu. %r3,%r8,%r9
   bl record
   li %r7,15
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   lis %r3,15
   li %r8,1
   sld %r8,%r8,%r31
   addis %r8,%r8,-7
   mulhwu. %r3,%r3,%r8
   bl record
   lis %r7,15
   addi %r7,%r7,-105
   bl check_alu_so_undef
0: lis %r8,0x1
   addi %r8,%r8,0x10
   lis %r7,0x1111
   mulhwu. %r3,%r8,%r7
   bl record
   li %r7,0x1112
   bl check_alu_undef
.if 0  # mulhwu. with OE=1 triggers an exception on the Cell, so we skip it.
0: lis %r3,0x6000
   addis %r3,%r3,0x6000
   mtxer %r3
   lis %r8,3
   lis %r9,5
   .int 0x7C694417  # mulhwu. %r3,%r9,%r8
   bl record
   li %r7,15
   bl check_alu_ov_undef
.endif

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - divd, divw
   ########################################################################

   # divd
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divd %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu
0: li %r9,-105
   li %r8,7
   divd %r3,%r9,%r8
   bl record
   li %r7,-15
   bl check_alu
0: li %r7,105
   li %r9,-7
   divd %r3,%r7,%r9
   bl record
   li %r7,-15
   bl check_alu
0: li %r7,3
   li %r8,-7
   divd %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu
0: li %r9,1
   sld %r9,%r9,%r31
   addi %r9,%r9,-105
   li %r7,7
   divd %r3,%r9,%r7
   bl record
   lis %r7,0x2492
   addi %r7,%r7,0x4915
   bl check_alu
0: li %r9,0
   divd %r3,%r9,%r9
   # This gives no result; just check that it doesn't crash.

   # divd.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divd. %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu_gt
0: li %r9,-105
   li %r8,7
   divd. %r3,%r9,%r8
   bl record
   li %r7,-15
   bl check_alu_lt
0: li %r7,3
   li %r8,-7
   divd. %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu_eq

   # divdo
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divdo %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu
0: li %r9,-105
   li %r8,7
   divdo %r3,%r9,%r8
   bl record
   li %r7,-15
   bl check_alu
0: li %r7,3
   li %r8,-7
   divdo %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r9,-1
   divdo %r3,%r7,%r9
   bl record
   li %r3,0         # The result is undefined, so skip the result check.
   li %r7,0
   bl check_alu_ov
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r11,1        # This is well-defined and should succeed.
   divdo %r3,%r7,%r11
   bl record
   bl check_alu
0: li %r8,1
   li %r7,0
   divdo %r3,%r8,%r7
   bl record
   li %r3,0
   bl check_alu_ov
0: li %r9,0
   divdo %r3,%r9,%r7
   bl record
   li %r3,0
   bl check_alu_ov

   # divdo.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divdo. %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu_gt
0: li %r9,-105
   li %r8,7
   divdo. %r3,%r9,%r8
   bl record
   li %r7,-15
   bl check_alu_lt
0: li %r7,3
   li %r8,-7
   divdo. %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r9,-1
   divdo. %r3,%r7,%r9
   bl record
   li %r3,0
   li %r7,0
   bl check_alu_ov_undef
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r11,1
   divdo. %r3,%r7,%r11
   bl record
   bl check_alu_lt
0: li %r8,1
   li %r7,0
   divdo. %r3,%r8,%r7
   bl record
   li %r3,0
   bl check_alu_ov_undef
0: li %r9,0
   divdo. %r3,%r9,%r7
   bl record
   li %r3,0
   bl check_alu_ov_undef

   # divw
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divw %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   # For divw instructions, the high 32 bits of the target register are
   # undefined, so shift them out of the way.
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,-105
   li %r8,7
   divw %r3,%r9,%r8
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,105
   li %r9,-7
   divw %r3,%r7,%r9
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,3
   li %r8,-7
   divw %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,1
   sld %r9,%r9,%r31
   addi %r9,%r9,-105
   li %r7,7
   divw %r3,%r9,%r7
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,0
   divw %r3,%r9,%r9
   # This gives no result; just check that it doesn't crash.

   # divw.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divw. %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   li %r9,-105
   li %r8,7
   divw. %r3,%r9,%r8
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_so_undef
0: li %r7,3
   li %r8,-7
   divw. %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef

   # divwo
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwo %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,-105
   li %r8,7
   divwo %r3,%r9,%r8
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,3
   li %r8,-7
   divwo %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r7,0x8000
   li %r9,-1
   divwo %r3,%r7,%r9
   bl record
   li %r3,0
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov
0: lis %r7,0x8000
   li %r11,1
   divwo %r3,%r7,%r11
   bl record
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r8,1
   li %r7,0
   divwo %r3,%r8,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov
0: li %r9,0
   divwo %r3,%r9,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov

   # divwo.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwo. %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   li %r9,-105
   li %r8,7
   divwo. %r3,%r9,%r8
   bl record
   li %r7,-15
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_so_undef
0: li %r7,3
   li %r8,-7
   divwo. %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r7,0x8000
   li %r9,-1
   divwo. %r3,%r7,%r9
   bl record
   li %r3,0
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov_undef
0: lis %r7,0x8000
   li %r11,1
   divwo. %r3,%r7,%r11
   bl record
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: li %r8,1
   li %r7,0
   divwo. %r3,%r8,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov_undef
0: li %r9,0
   divwo. %r3,%r9,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov_undef

   ########################################################################
   # 3.3.8 Fixed-Point Arithmetic Instructions - divdu, divwu
   ########################################################################

0: lis %r24,0x2492    # (uint64_t)-105 / 7
   addi %r24,%r24,0x4925
   sld %r24,%r24,%r31
   addis %r24,%r24,0x9249
   addi %r24,%r24,0x2483

   # divdu
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divdu %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu
0: li %r9,-105
   li %r8,7
   divdu %r3,%r9,%r8
   bl record
   mr %r7,%r24
   bl check_alu
0: li %r7,105
   li %r9,-7
   divdu %r3,%r7,%r9
   bl record
   li %r7,0
   bl check_alu

   # divdu.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divdu. %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu_gt
0: li %r9,-105
   li %r8,1
   divdu. %r3,%r9,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r7,105
   li %r8,-7
   divdu. %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu_eq

   # divduo
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divduo %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu
0: li %r9,-105
   li %r8,7
   divduo %r3,%r9,%r8
   bl record
   mr %r7,%r24
   bl check_alu
0: li %r7,105
   li %r8,-7
   divduo %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r9,-1
   divduo %r3,%r7,%r9
   bl record
   li %r7,0
   bl check_alu
0: li %r8,1
   divduo %r3,%r8,%r7
   bl record
   li %r3,0
   bl check_alu_ov
0: li %r9,0
   divduo %r3,%r9,%r7
   bl record
   li %r3,0
   bl check_alu_ov

   # divduo.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divduo. %r3,%r8,%r9
   bl record
   lis %r7,0x2C00
   bl check_alu_gt
0: li %r9,-105
   li %r8,1
   divduo. %r3,%r9,%r8
   bl record
   li %r7,-105
   bl check_alu_lt
0: li %r7,105
   li %r8,-7
   divduo. %r3,%r7,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r7,0x8000
   sld %r7,%r7,%r31
   li %r9,-1
   divduo. %r3,%r7,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r8,1
   divduo. %r3,%r8,%r7
   bl record
   li %r3,0
   bl check_alu_ov_undef
0: li %r9,0
   divduo. %r3,%r9,%r7
   bl record
   li %r3,0
   bl check_alu_ov_undef

   # divwu
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwu %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,-105
   li %r8,7
   divwu %r3,%r9,%r8
   bl record
   lis %r7,0x2492
   addi %r7,%r7,0x4915
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,105
   li %r9,-7
   divwu %r3,%r7,%r9
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,105
   li %r8,-7
   divwu %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,1
   sld %r9,%r9,%r31
   addi %r9,%r9,-105
   li %r7,7
   divwu %r3,%r9,%r7
   bl record
   lis %r7,0x2492
   addi %r7,%r7,0x4915
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu

   # divwu.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwu. %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   li %r9,-105
   li %r8,1
   divwu. %r3,%r9,%r8
   bl record
   li %r7,-105
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_so_undef
0: li %r7,105
   li %r8,-7
   divwu. %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef

   # divwuo
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwuo %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r9,-105
   li %r8,7
   divwuo %r3,%r9,%r8
   bl record
   lis %r7,0x2492
   addi %r7,%r7,0x4915
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r7,105
   li %r8,-7
   divwuo %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: lis %r7,0x8000
   li %r9,-1
   divwuo %r3,%r7,%r9
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu
0: li %r8,1
   divwuo %r3,%r8,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov
0: li %r9,0
   divwuo %r3,%r9,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov

   # divwuo.
0: li %r8,33
   li %r0,28
   sld %r8,%r8,%r0
   li %r9,12
   divwuo. %r3,%r8,%r9
   bl record
   lis %r7,0x155
   addi %r7,%r7,0x5555
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r3,0x4000
   addis %r3,%r3,0x4000
   mtxer %r3
   li %r9,-105
   li %r8,1
   divwuo. %r3,%r9,%r8
   bl record
   li %r7,-105
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_so_undef
0: li %r7,105
   li %r8,-7
   divwuo. %r3,%r7,%r8
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: lis %r7,0x8000
   li %r9,-1
   divwuo. %r3,%r7,%r9
   bl record
   li %r7,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_undef
0: li %r8,1
   divwuo. %r3,%r8,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov_undef
0: li %r9,0
   divwuo. %r3,%r9,%r7
   bl record
   li %r3,0
   sld %r3,%r3,%r31
   sld %r7,%r7,%r31
   bl check_alu_ov_undef

   ########################################################################
   # 3.3.9 Fixed-Point Compare Instructions
   ########################################################################

   # These instructions don't produce any results, but we use the check_alu
   # functions anyway for brevity, so set up parameters to avoid spurious
   # failures.
0: li %r3,0
   li %r7,0

   # cmpdi
0: li %r11,3
   cmpdi %r11,4
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   cmpdi %r11,3
   bl record
   bl check_alu_ov_eq
0: cmpdi %r11,2
   bl record
   bl check_alu_gt
0: cmpdi %r11,-1
   bl record
   bl check_alu_gt
0: li %r11,0
   cmpdi %r11,1
   bl record
   bl check_alu_lt
0: cmpdi %r11,0
   bl record
   bl check_alu_eq
0: cmpdi %r11,-1
   bl record
   bl check_alu_gt
0: li %r11,-3
   cmpdi %r11,0
   bl record
   bl check_alu_lt
0: cmpdi %r11,-2
   bl record
   bl check_alu_lt
0: cmpdi %r11,-3
   bl record
   bl check_alu_eq
0: cmpdi %r11,-4
   bl record
   bl check_alu_gt
0: li %r11,0
   cmpdi cr6,%r11,0
   bl record
   mfcr %r8
   cmpdi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   cmpdi %r11,-3
   bl record
   bl check_alu_gt

   # cmpwi
0: li %r11,3
   cmpwi %r11,4
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   cmpwi %r11,3
   bl record
   bl check_alu_ov_eq
0: cmpwi %r11,2
   bl record
   bl check_alu_gt
0: cmpwi %r11,-1
   bl record
   bl check_alu_gt
0: li %r11,0
   cmpwi %r11,1
   bl record
   bl check_alu_lt
0: cmpwi %r11,0
   bl record
   bl check_alu_eq
0: cmpwi %r11,-1
   bl record
   bl check_alu_gt
0: li %r11,-3
   cmpwi %r11,0
   bl record
   bl check_alu_lt
0: cmpwi %r11,-2
   bl record
   bl check_alu_lt
0: cmpwi %r11,-3
   bl record
   bl check_alu_eq
0: cmpwi %r11,-4
   bl record
   bl check_alu_gt
0: li %r11,0
   cmpwi cr6,%r11,0
   bl record
   mfcr %r8
   cmpdi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   cmpwi %r11,-3
   bl record
   bl check_alu_eq

   # cmpd
0: li %r11,3
   li %r9,4
   cmpd %r11,%r9
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   li %r9,3
   cmpd %r11,%r9
   bl record
   bl check_alu_ov_eq
0: li %r9,2
   cmpd %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-1
   cmpd %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,1
   cmpd %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,0
   cmpd %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-1
   cmpd %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,-3
   li %r9,0
   cmpd %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-2
   cmpd %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-3
   cmpd %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-4
   cmpd %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,0
   cmpd cr6,%r11,%r9
   bl record
   mfcr %r8
   cmpdi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   li %r9,-3
   cmpd %r11,%r9
   bl record
   bl check_alu_gt

   # cmpw
0: li %r11,3
   li %r9,4
   cmpw %r11,%r9
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   li %r9,3
   cmpw %r11,%r9
   bl record
   bl check_alu_ov_eq
0: li %r9,2
   cmpw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-1
   cmpw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,1
   cmpw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,0
   cmpw %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-1
   cmpw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,-3
   li %r9,0
   cmpw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-2
   cmpw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-3
   cmpw %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-4
   cmpw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,0
   cmpw cr6,%r11,%r9
   bl record
   mfcr %r8
   cmpdi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   li %r9,-3
   cmpw %r11,%r9
   bl record
   bl check_alu_eq

   # cmpldi
0: li %r11,3
   cmpldi %r11,4
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   cmpldi %r11,3
   bl record
   bl check_alu_ov_eq
0: cmpldi %r11,2
   bl record
   bl check_alu_gt
0: cmpldi %r11,65536-1
   bl record
   bl check_alu_lt
0: li %r11,0
   cmpldi %r11,1
   bl record
   bl check_alu_lt
0: cmpldi %r11,0
   bl record
   bl check_alu_eq
0: cmpldi %r11,65536-1
   bl record
   bl check_alu_lt
0: li %r11,-3
   cmpldi %r11,0
   bl record
   bl check_alu_gt
0: cmpldi %r11,65536-2
   bl record
   bl check_alu_gt
0: cmpldi %r11,65536-3
   bl record
   bl check_alu_gt
0: cmpldi %r11,65536-4
   bl record
   bl check_alu_gt
0: li %r11,0
   cmpldi cr6,%r11,0
   bl record
   mfcr %r8
   cmpldi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   cmpldi %r11,65536-3
   bl record
   bl check_alu_gt

   # cmplwi
0: li %r11,3
   cmplwi %r11,4
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   cmplwi %r11,3
   bl record
   bl check_alu_ov_eq
0: cmplwi %r11,2
   bl record
   bl check_alu_gt
0: cmplwi %r11,65536-1
   bl record
   bl check_alu_lt
0: li %r11,0
   cmplwi %r11,1
   bl record
   bl check_alu_lt
0: cmplwi %r11,0
   bl record
   bl check_alu_eq
0: cmplwi %r11,65536-1
   bl record
   bl check_alu_lt
0: li %r11,-3
   cmplwi %r11,0
   bl record
   bl check_alu_gt
0: cmplwi %r11,65536-2
   bl record
   bl check_alu_gt
0: cmplwi %r11,65536-3
   bl record
   bl check_alu_gt
0: cmplwi %r11,65536-4
   bl record
   bl check_alu_gt
0: li %r11,0
   cmplwi cr6,%r11,0
   bl record
   mfcr %r8
   cmpldi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   cmplwi %r11,65536-3
   bl record
   bl check_alu_gt

   # cmpld
0: li %r11,3
   li %r9,4
   cmpld %r11,%r9
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   li %r9,3
   cmpld %r11,%r9
   bl record
   bl check_alu_ov_eq
0: li %r9,2
   cmpld %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-1
   cmpld %r11,%r9
   bl record
   bl check_alu_lt
0: li %r11,0
   li %r9,1
   cmpld %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,0
   cmpld %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-1
   cmpld %r11,%r9
   bl record
   bl check_alu_lt
0: li %r11,-3
   li %r9,0
   cmpld %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-2
   cmpld %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-3
   cmpld %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-4
   cmpld %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,0
   cmpld cr6,%r11,%r9
   bl record
   mfcr %r8
   cmpldi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   li %r9,-3
   cmpld %r11,%r9
   bl record
   bl check_alu_lt

   # cmplw
0: li %r11,3
   li %r9,4
   cmplw %r11,%r9
   bl record
   bl check_alu_lt
0: lis %r8,0x6000
   addis %r8,%r8,0x6000
   mtxer %r8
   li %r9,3
   cmplw %r11,%r9
   bl record
   bl check_alu_ov_eq
0: li %r9,2
   cmplw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-1
   cmplw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r11,0
   li %r9,1
   cmplw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,0
   cmplw %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-1
   cmplw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r11,-3
   li %r9,0
   cmplw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r9,-2
   cmplw %r11,%r9
   bl record
   bl check_alu_lt
0: li %r9,-3
   cmplw %r11,%r9
   bl record
   bl check_alu_eq
0: li %r9,-4
   cmplw %r11,%r9
   bl record
   bl check_alu_gt
0: li %r11,0
   li %r9,0
   cmplw cr6,%r11,%r9
   bl record
   mfcr %r8
   cmpldi %r8,0x20
   beq 0f
   std %r8,8(%r6)
   addi %r6,%r6,32
0: mtcr %r7
   li %r11,1
   sld %r11,%r11,%r31
   addi %r11,%r11,-3
   li %r9,-3
   cmplw %r11,%r9
   bl record
   bl check_alu_eq

   ########################################################################
   # 3.3.10 Fixed-Point Trap Instructions
   ########################################################################

.if TEST_TRAP

   # tdi
0: li %r7,10
   li %r3,-1
   tdi 16,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 2,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 13,%r7,11
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 31,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 8,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 1,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 22,%r7,9
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 31,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 4,%r7,10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 27,%r7,10
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 31,%r7,10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 8,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 2,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 21,%r7,-10
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 31,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   sld %r7,%r7,%r31
   li %r3,-1
   tdi 8,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 1,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 22,%r7,1
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tdi 31,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # twi
0: li %r7,10
   li %r3,-1
   twi 16,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 2,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 13,%r7,11
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 31,%r7,11
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 8,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 1,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 22,%r7,9
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 31,%r7,9
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 4,%r7,10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 27,%r7,10
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 31,%r7,10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 8,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 2,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 21,%r7,-10
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 31,%r7,-10
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1         # This bit will be ignored.
   sld %r7,%r7,%r31
   li %r3,-1
   twi 16,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 2,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 13,%r7,1
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   twi 31,%r7,1
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # td
0: li %r7,10
   li %r24,11
   li %r3,-1
   td 16,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 2,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 13,%r7,%r24
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r25,9
   li %r3,-1
   td 8,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 1,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 22,%r7,%r25
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r26,10
   li %r3,-1
   td 4,%r7,%r26
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 27,%r7,%r26
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r26
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r27,-10
   li %r3,-1
   td 8,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 2,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 21,%r7,%r27
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   sld %r7,%r7,%r31
   li %r28,1
   li %r3,-1
   td 8,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 1,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 22,%r7,%r28
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   li %r29,1
   sld %r29,%r29,%r31
   li %r3,-1
   td 16,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 2,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 13,%r7,%r29
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   td 31,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # tw
0: li %r7,10
   li %r24,11
   li %r3,-1
   tw 16,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 2,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 13,%r7,%r24
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r24
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r25,9
   li %r3,-1
   tw 8,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 1,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 22,%r7,%r25
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r25
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r26,10
   li %r3,-1
   tw 4,%r7,%r26
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 27,%r7,%r26
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r26
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r27,-10
   li %r3,-1
   tw 8,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 2,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 21,%r7,%r27
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r27
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   sld %r7,%r7,%r31
   li %r28,1
   li %r3,-1
   tw 16,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 2,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 13,%r7,%r28
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r28
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   li %r29,1
   sld %r29,%r29,%r31
   li %r3,-1
   tw 8,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 1,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 22,%r7,%r29
   bl record
   cmpdi %r3,-1
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,-1
   tw 31,%r7,%r29
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

.endif  # TEST_TRAP

   ########################################################################
   # 3.3.11 Fixed-Point Logical Instructions - second operand immediate
   ########################################################################

0: lis %r24,0x55AA
   addi %r24,%r24,0x55AA
   # We want to load 0xAA55AA55, but addi ...,0xAA55 will subtract from the
   # high halfword, so we use 0xAA56 (split into lis+addis to keep the
   # upper 32 bits clear).  Normally we'd use ori instead of addi, but we
   # haven't yet confirmed that ori functions properly.
   lis %r25,0x5A56
   addis %r25,%r25,0x5000
   addi %r25,%r25,0xAA55-0x10000

   # andi.
0: andi. %r3,%r24,0x1248
   bl record
   li %r7,0x1008
   bl check_alu_gt
0: andi. %r3,%r24,0xFFFF
   bl record
   li %r7,0x55AA
   bl check_alu_gt
0: andi. %r3,%r24,0
   bl record
   li %r7,0
   bl check_alu_eq

   # andis.
0: andis. %r3,%r24,0x1248
   bl record
   lis %r7,0x1008
   bl check_alu_gt
0: andis. %r3,%r25,0xFFFF
   bl record
   lis %r7,0x5A55
   addis %r7,%r7,0x5000
   bl check_alu_gt
0: andis. %r3,%r24,0
   bl record
   li %r7,0
   bl check_alu_eq

   # ori
0: ori %r3,%r24,0x1248
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x57EA
   bl check_alu

   # oris
0: oris %r3,%r24,0x1248
   bl record
   lis %r7,0x57EA
   addi %r7,%r7,0x55AA
   bl check_alu

   # xori
0: xori %r3,%r24,0x1248
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x47E2
   bl check_alu

   # xoris
0: xoris %r3,%r24,0x1248
   bl record
   lis %r7,0x47E2
   addi %r7,%r7,0x55AA
   bl check_alu

   ########################################################################
   # 3.3.11 Fixed-Point Logical Instructions - second operand in register
   ########################################################################

   # and
0: li %r3,0x1248
   and %r3,%r24,%r3
   bl record
   li %r7,0x1008
   bl check_alu

   # and.
0: li %r11,-6
   li %r3,3
   and. %r3,%r11,%r3
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r8,5
   and. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-3
   and. %r3,%r11,%r9
   bl record
   li %r7,-8
   bl check_alu_lt

   # or
0: li %r3,0x1248
   or %r3,%r24,%r3
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x57EA
   bl check_alu

   # or.
0: li %r11,6
   li %r3,3
   or. %r3,%r11,%r3
   bl record
   li %r7,7
   bl check_alu_gt
0: li %r8,0
   or. %r3,%r8,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-6
   or. %r3,%r11,%r9
   bl record
   li %r7,-2
   bl check_alu_lt

   # xor
0: li %r3,0x1248
   xor %r3,%r24,%r3
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x47E2
   bl check_alu

   # xor.
0: li %r11,-6
   li %r3,3
   xor. %r3,%r11,%r3
   bl record
   li %r7,-7
   bl check_alu_lt
0: li %r8,-6
   xor. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-3
   xor. %r3,%r11,%r9
   bl record
   li %r7,7
   bl check_alu_gt

   # nand
0: li %r3,0x1248
   nand %r3,%r24,%r3
   bl record
   li %r7,~0x1008
   bl check_alu

   # nand.
0: li %r11,-6
   li %r3,3
   nand. %r3,%r11,%r3
   bl record
   li %r7,-3
   bl check_alu_lt
0: li %r8,-1
   nand. %r3,%r8,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-3
   nand. %r3,%r11,%r9
   bl record
   li %r7,7
   bl check_alu_gt

   # nor
0: li %r3,0x1248
   nor %r3,%r24,%r3
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x57EA
   nand %r7,%r7,%r7 # "not" is converted to "nor" so we can't use it yet.
   bl check_alu

   # nor.
0: li %r11,6
   li %r3,3
   nor. %r3,%r11,%r3
   bl record
   li %r7,-8
   bl check_alu_lt
0: li %r8,-1
   nor. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-6
   nor. %r3,%r11,%r9
   bl record
   li %r7,1
   bl check_alu_gt

   # eqv
0: li %r3,0x1248
   eqv %r3,%r24,%r3
   bl record
   lis %r7,0x55AA
   addi %r7,%r7,0x47E2
   not %r7,%r7
   bl check_alu

   # eqv.
0: li %r11,-6
   li %r3,3
   eqv. %r3,%r11,%r3
   bl record
   li %r7,6
   bl check_alu_gt
0: li %r8,5
   eqv. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-3
   eqv. %r3,%r11,%r9
   bl record
   li %r7,-8
   bl check_alu_lt

   # andc
0: li %r3,0x1248
   andc %r3,%r3,%r25
   bl record
   li %r7,0x1008
   bl check_alu

   # andc.
0: li %r11,5
   li %r3,3
   andc. %r3,%r3,%r11
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r8,5
   andc. %r3,%r8,%r11
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-3
   andc. %r3,%r9,%r11
   bl record
   li %r7,-8
   bl check_alu_lt

   # orc
0: li %r3,0x1248
   orc %r3,%r3,%r25
   bl record
   li %r7,-1
   sld %r7,%r7,%r31
   addis %r7,%r7,0x55AA
   addi %r7,%r7,0x57EA
   bl check_alu

   # orc.
0: li %r11,-7
   li %r3,3
   orc. %r3,%r3,%r11
   bl record
   li %r7,7
   bl check_alu_gt
0: li %r8,-1
   li %r9,0
   orc. %r3,%r9,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,-6
   orc. %r3,%r9,%r11
   bl record
   li %r7,-2
   bl check_alu_lt

   ########################################################################
   # 3.3.11 Fixed-Point Logical Instructions - extsb, extsh, extsw
   ########################################################################

   # extsb
0: li %r3,0x17F
   extsb %r3,%r3
   bl record
   li %r7,0x7F
   bl check_alu
0: li %r3,0x180
   extsb %r3,%r3
   bl record
   li %r7,-0x80
   bl check_alu

   # extsb.
0: li %r3,0x17F
   extsb. %r3,%r3
   bl record
   li %r7,0x7F
   bl check_alu_gt
0: li %r3,0x180
   extsb. %r3,%r3
   bl record
   li %r7,-0x80
   bl check_alu_lt
0: li %r3,0x100
   extsb. %r3,%r3
   bl record
   li %r7,0
   bl check_alu_eq

   # extsh
0: li %r11,8
   li %r3,0x17F
   sld %r3,%r3,%r11
   extsh %r3,%r3
   bl record
   li %r7,0x7F00
   bl check_alu
0: li %r3,0x180
   sld %r3,%r3,%r11
   extsh %r3,%r3
   bl record
   li %r7,-0x8000
   bl check_alu

   # extsh.
0: li %r3,0x17F
   sld %r3,%r3,%r11
   extsh. %r3,%r3
   bl record
   li %r7,0x7F00
   bl check_alu_gt
0: li %r3,0x180
   sld %r3,%r3,%r11
   extsh. %r3,%r3
   bl record
   li %r7,-0x8000
   bl check_alu_lt
0: li %r3,0x100
   sld %r3,%r3,%r11
   extsh. %r3,%r3
   bl record
   li %r7,0
   bl check_alu_eq

   # extsw
0: li %r11,24
   li %r3,0x17F
   sld %r3,%r3,%r11
   extsw %r3,%r3
   bl record
   lis %r7,0x7F00
   bl check_alu
0: li %r3,0x180
   sld %r3,%r3,%r11
   extsw %r3,%r3
   bl record
   lis %r7,-0x8000
   bl check_alu

   # extsw.
0: li %r3,0x17F
   sld %r3,%r3,%r11
   extsw. %r3,%r3
   bl record
   lis %r7,0x7F00
   bl check_alu_gt
0: li %r3,0x180
   sld %r3,%r3,%r11
   extsw. %r3,%r3
   bl record
   lis %r7,-0x8000
   bl check_alu_lt
0: li %r3,0x100
   sld %r3,%r3,%r11
   extsw. %r3,%r3
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.11 Fixed-Point Logical Instructions - cnltzd, cntlzw, popcntb
   ########################################################################

   # cntlzd
0: li %r3,1
   cntlzd %r3,%r3
   bl record
   li %r7,63
   bl check_alu
0: li %r8,-1
   cntlzd %r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: li %r9,0
   cntlzd %r3,%r9
   bl record
   li %r7,64
   bl check_alu

   # cntlzd.
0: li %r3,1
   cntlzd. %r3,%r3
   bl record
   li %r7,63
   bl check_alu_gt
0: li %r8,-1
   cntlzd. %r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,0
   cntlzd. %r3,%r9
   bl record
   li %r7,64
   bl check_alu_gt

   # cntlzw
0: li %r3,1
   cntlzw %r3,%r3
   bl record
   li %r7,31
   bl check_alu
0: li %r8,-1
   cntlzw %r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: li %r9,0
   cntlzw %r3,%r9
   bl record
   li %r7,32
   bl check_alu

   # cntlzw.
0: li %r3,1
   cntlzw. %r3,%r3
   bl record
   li %r7,31
   bl check_alu_gt
0: li %r8,-1
   cntlzw. %r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r9,0
   cntlzw. %r3,%r9
   bl record
   li %r7,32
   bl check_alu_gt

   # popcntb is not implemented on the Cell.

   ########################################################################
   # 3.3.12.1 Fixed-Point Rotate and Shift Instructions - rldicl, rldicr, rldic
   ########################################################################

0: lis %r24,0x123
   ori %r24,%r24,0x4567
   sld %r24,%r24,%r31
   oris %r24,%r24,0x89AB
   ori %r24,%r24,0xCDEF
   lis %r25,0x8000          # Copy with high bit set to check for mask overrun.
   sld %r25,%r25,%r31
   or %r25,%r25,%r24

   # rldicl
0: rldicl %r3,%r24,36,0     # rotldi %r3,%r24,36
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF0
   sld %r7,%r7,%r31
   oris %r7,%r7,0x1234
   ori %r7,%r7,0x5678
   bl check_alu
0: rldicl %r3,%r24,32,63    # extrdi %r3,%r24,1,31
   bl record
   li %r7,1
   bl check_alu

   # rldicl.
0: rldicl. %r3,%r24,36,0    # rotldi. %r3,%r24,36
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF0
   sld %r7,%r7,%r31
   oris %r7,%r7,0x1234
   ori %r7,%r7,0x5678
   bl check_alu_lt
0: rldicl. %r3,%r24,32,63   # extrdi. %r3,%r24,1,31
   bl record
   li %r7,1
   bl check_alu_gt
0: rldicl. %r3,%r24,17,63   # extrdi. %r3,%r24,1,16
   bl record
   li %r7,0
   bl check_alu_eq

   # rldicr
0: rldicr %r3,%r24,40,63    # rotldi %r3,%r24,40
   bl record
   lis %r7,0xABCD
   ori %r7,%r7,0xEF01
   sld %r7,%r7,%r31
   oris %r7,%r7,0x2345
   ori %r7,%r7,0x6789
   bl check_alu
0: rldicr %r3,%r24,20,1     # extldi %r3,%r24,2,20
   bl record
   lis %r7,0x4000
   sld %r7,%r7,%r31
   bl check_alu

   # rldicr.
0: rldicr. %r3,%r24,40,63   # rotldi. %r3,%r24,40
   bl record
   lis %r7,0xABCD
   ori %r7,%r7,0xEF01
   sld %r7,%r7,%r31
   oris %r7,%r7,0x2345
   ori %r7,%r7,0x6789
   bl check_alu_lt
0: rldicr. %r3,%r24,20,1    # extldi. %r3,%r24,2,20
   bl record
   lis %r7,0x4000
   sld %r7,%r7,%r31
   bl check_alu_gt
0: rldicr. %r3,%r24,16,0    # extldi. %r3,%r24,1,16
   bl record
   li %r7,0
   bl check_alu_eq

   # rldic
0: rldic %r3,%r24,44,20     # rotldi %r3,%r24,44
   bl record
   lis %r7,0xBCDE
   ori %r7,%r7,0xF012
   sld %r7,%r7,%r31
   oris %r7,%r7,0x3456
   ori %r7,%r7,0x789A
   bl check_alu
0: rldic %r3,%r25,1,62
   bl record
   li %r7,2
   bl check_alu
0: rldic %r3,%r25,63,63     # Check mask wraparound.
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   ori %r7,%r7,0x0001
   bl check_alu

   # rldic.
0: rldic. %r3,%r24,44,20    # rotldi. %r3,%r24,44
   bl record
   lis %r7,0xBCDE
   ori %r7,%r7,0xF012
   sld %r7,%r7,%r31
   oris %r7,%r7,0x3456
   ori %r7,%r7,0x789A
   bl check_alu_lt
0: rldic. %r3,%r25,1,62
   bl record
   li %r7,2
   bl check_alu_gt
0: xori %r7,%r25,1
   rldic. %r3,%r7,1,62
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.12.1 Fixed-Point Rotate and Shift Instructions - rldcl, rldcr
   ########################################################################

   # rldcl
0: li %r0,36
   rldcl %r3,%r24,%r0,0     # rotld %r3,%r24,%r0
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF0
   sld %r7,%r7,%r31
   oris %r7,%r7,0x1234
   ori %r7,%r7,0x5678
   bl check_alu
0: li %r0,32
   rldcl %r3,%r24,%r0,63
   bl record
   li %r7,1
   bl check_alu

   # rldcl.
0: li %r0,36
   rldcl. %r3,%r24,%r0,0    # rotld. %r3,%r24,%r0
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF0
   sld %r7,%r7,%r31
   oris %r7,%r7,0x1234
   ori %r7,%r7,0x5678
   bl check_alu_lt
0: li %r0,32
   rldcl. %r3,%r24,%r0,63
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r3,17
   rldcl. %r3,%r24,%r3,63
   bl record
   li %r7,0
   bl check_alu_eq

   # rldcr
0: li %r3,40
   rldcr %r3,%r24,%r3,63    # rotld %r3,%r24,%r3
   bl record
   lis %r7,0xABCD
   ori %r7,%r7,0xEF01
   sld %r7,%r7,%r31
   oris %r7,%r7,0x2345
   ori %r7,%r7,0x6789
   bl check_alu
0: li %r0,20
   rldcr %r3,%r24,%r0,1
   bl record
   lis %r7,0x4000
   sld %r7,%r7,%r31
   bl check_alu

   # rldcr.
0: li %r3,40
   rldcr. %r3,%r24,%r3,63   # rotld. %r3,%r24,%r3
   bl record
   lis %r7,0xABCD
   ori %r7,%r7,0xEF01
   sld %r7,%r7,%r31
   oris %r7,%r7,0x2345
   ori %r7,%r7,0x6789
   bl check_alu_lt
0: li %r0,20
   rldcr. %r3,%r24,%r0,1
   bl record
   lis %r7,0x4000
   sld %r7,%r7,%r31
   bl check_alu_gt
0: li %r0,16
   rldcr. %r3,%r24,%r0,0
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.12.1 Fixed-Point Rotate and Shift Instructions - rlwinm, rlwnm
   ########################################################################

   # rlwinm
0: rlwinm %r3,%r24,4,0,31   # rotlwi %r3,%r24,4
   bl record
   lis %r7,0x5ABC
   addis %r7,%r7,0x4000
   ori %r7,%r7,0xDEF8
   bl check_alu
0: rlwinm %r3,%r24,30,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xC000
   ori %r7,%r7,0x0001
   bl check_alu

   # rlwinm.
0: rlwinm. %r3,%r24,4,0,31  # rotlwi. %r3,%r24,4
   bl record
   lis %r7,0x5ABC
   addis %r7,%r7,0x4000
   ori %r7,%r7,0xDEF8
   bl check_alu_gt
0: rlwinm. %r3,%r24,30,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xC000
   ori %r7,%r7,0x0001
   bl check_alu_lt
0: rlwinm. %r3,%r24,5,28,30
   bl record
   li %r7,0
   bl check_alu_eq

   # rlwnm
0: li %r0,4
   rlwnm %r3,%r24,%r0,0,31  # rotlw %r3,%r24,%r0
   bl record
   lis %r7,0x5ABC
   addis %r7,%r7,0x4000
   ori %r7,%r7,0xDEF8
   bl check_alu
0: li %r0,30
   rlwnm %r3,%r24,%r0,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xC000
   ori %r7,%r7,0x0001
   bl check_alu

   # rlwnm.
0: li %r0,4
   rlwnm. %r3,%r24,%r0,0,31 # rotlw. %r3,%r24,%r0
   bl record
   lis %r7,0x5ABC
   addis %r7,%r7,0x4000
   ori %r7,%r7,0xDEF8
   bl check_alu_gt
0: li %r0,30
   rlwnm. %r3,%r24,%r0,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xC000
   ori %r7,%r7,0x0001
   bl check_alu_lt
0: li %r0,5
   rlwnm. %r3,%r24,%r0,28,30
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.12.1 Fixed-Point Rotate and Shift Instructions - rldimi
   ########################################################################

   # rldimi
0: li %r3,-1
   rldimi %r3,%r24,36,28
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF0
   sld %r7,%r7,%r31
   oris %r7,%r7,0x1234
   ori %r7,%r7,0x5678
   bl check_alu
0: li %r3,0
   rldimi %r3,%r25,62,63
   bl record
   lis %r7,0xC000
   sld %r7,%r7,%r31
   ori %r7,%r7,0x0001
   bl check_alu

   # rldimi.
0: li %r3,-1
   rldimi. %r3,%r24,28,36
   bl record
   lis %r7,0x789A
   ori %r7,%r7,0xBCDE
   sld %r7,%r7,%r31
   oris %r7,%r7,0xF012
   ori %r7,%r7,0x3456
   bl check_alu_gt
0: li %r3,0
   rldimi. %r3,%r25,62,63
   bl record
   lis %r7,0xC000
   sld %r7,%r7,%r31
   ori %r7,%r7,0x0001
   bl check_alu_lt
0: xori %r7,%r25,1
   li %r3,2
   rldimi. %r3,%r7,1,62
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.12.1 Fixed-Point Rotate and Shift Instructions - rlwimi
   ########################################################################

   # rlwimi
0: li %r3,-1
   rlwimi %r3,%r24,4,0,31
   bl record
   lis %r7,0x9ABC
   ori %r7,%r7,0xDEF8
   bl check_alu
0: lis %r3,0x1000
   ori %r3,%r3,0x0004
   rlwimi %r3,%r24,30,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xD000
   ori %r7,%r7,0x0005
   bl check_alu

   # rlwimi.
0: lis %r3,0x4000
   oris %r3,%r3,0x0001
   sld %r3,%r3,%r31
   mr %r7,%r3
   rlwimi. %r3,%r24,4,0,31
   bl record
   oris %r7,%r7,0x9ABC
   ori %r7,%r7,0xDEF8
   bl check_alu_gt
0: lis %r3,0x1000
   ori %r3,%r3,0x0004
   rlwimi. %r3,%r24,30,31,1
   bl record
   lis %r7,0xE26A
   ori %r7,%r7,0xF37B
   sld %r7,%r7,31
   oris %r7,%r7,0xD000
   ori %r7,%r7,0x0005
   bl check_alu_lt
0: li %r3,14
   rlwimi. %r3,%r24,5,28,30
   bl record
   li %r7,0
   bl check_alu_eq

   ########################################################################
   # 3.3.12.2 Fixed-Point Rotate and Shift Instructions - sld, slw
   ########################################################################

0: lis %r24,0x8000
   sld %r24,%r24,%r31
   li %r25,1
   sld %r25,%r25,%r31
   oris %r25,%r25,0x8000
   lis %r26,0x4000
   addis %r26,%r26,0x4000
   lis %r27,0xA000
   sld %r27,%r27,%r31

   # sld
   # sld for a shift count less than 64 was tested above.
0: li %r3,1
   li %r8,64
   sld %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: li %r3,1
   li %r9,127
   sld %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu
0: li %r3,1
   li %r11,128
   sld %r3,%r3,%r11
   bl record
   li %r7,1
   bl check_alu

   # sld.
0: li %r3,1
   li %r0,0
   sld. %r3,%r3,%r0
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r3,1
   li %r7,63
   sld. %r3,%r3,%r7
   bl record
   lis %r7,0x8000
   sld %r7,%r7,%r31
   bl check_alu_lt
0: li %r3,1
   li %r8,64
   sld. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r3,1
   li %r9,127
   sld. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r3,1
   li %r11,128
   sld. %r3,%r3,%r11
   bl record
   li %r7,1
   bl check_alu_gt

   # slw
0: li %r3,1
   li %r0,0
   slw %r3,%r3,%r0
   bl record
   li %r7,1
   bl check_alu
0: li %r3,3
   li %r7,31
   slw %r3,%r3,%r7
   bl record
   mr %r7,%r26
   bl check_alu
0: li %r3,1
   li %r8,32
   slw %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: li %r3,1
   li %r9,63
   slw %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu
0: li %r3,1
   li %r11,64
   slw %r3,%r3,%r11
   bl record
   li %r7,1
   bl check_alu

   # slw.
0: li %r3,1
   li %r0,0
   slw. %r3,%r3,%r0
   bl record
   li %r7,1
   bl check_alu_gt
0: li %r3,3
   li %r7,31
   slw. %r3,%r3,%r7
   bl record
   mr %r7,%r26
   bl check_alu_gt
0: li %r3,1
   li %r8,32
   slw. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r3,1
   li %r9,63
   slw. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: li %r3,1
   li %r11,64
   slw. %r3,%r3,%r11
   bl record
   li %r7,1
   bl check_alu_gt

   ########################################################################
   # 3.3.12.2 Fixed-Point Rotate and Shift Instructions - srd, srw
   ########################################################################

   # srd
   # srd for a shift count less than 64 was tested above.
0: mr %r3,%r24
   li %r8,64
   srd %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r24
   li %r9,127
   srd %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r24
   li %r11,128
   srd %r3,%r3,%r11
   bl record
   mr %r7,%r24
   bl check_alu

   # srd.
0: mr %r3,%r24
   li %r0,0
   srd. %r3,%r3,%r0
   bl record
   mr %r7,%r24
   bl check_alu_lt
0: mr %r3,%r24
   li %r7,63
   srd. %r3,%r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: mr %r3,%r24
   li %r8,64
   srd. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r24
   li %r9,127
   srd. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r24
   li %r11,128
   srd. %r3,%r3,%r11
   bl record
   mr %r7,%r24
   bl check_alu_lt

   # srw
0: mr %r3,%r25
   li %r0,0
   srw %r3,%r3,%r0
   bl record
   mr %r7,%r26
   bl check_alu
0: mr %r3,%r25
   li %r7,31
   srw %r3,%r3,%r7
   bl record
   li %r7,1
   bl check_alu
0: mr %r3,%r25
   li %r8,32
   srw %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r25
   li %r9,63
   srw %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r25
   li %r11,64
   srw %r3,%r3,%r11
   bl record
   mr %r7,%r26
   bl check_alu

   # srw.
0: mr %r3,%r25
   li %r0,0
   srw. %r3,%r3,%r0
   bl record
   mr %r7,%r26
   bl check_alu_gt
0: mr %r3,%r25
   li %r7,31
   srw. %r3,%r3,%r7
   bl record
   li %r7,1
   bl check_alu_gt
0: mr %r3,%r25
   li %r8,32
   srw. %r3,%r3,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r25
   li %r9,63
   srw. %r3,%r3,%r9
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r25
   li %r11,64
   srw. %r3,%r3,%r11
   bl record
   mr %r7,%r26
   bl check_alu_gt

   ########################################################################
   # 3.3.12.2 Fixed-Point Rotate and Shift Instructions - sradi, srawi
   ########################################################################

   # sradi
0: li %r11,10
   sradi %r3,%r11,0
   bl record
   li %r7,10
   bl check_alu
0: li %r11,10
   sradi %r3,%r11,2
   bl record
   li %r7,2
   bl check_alu
0: li %r11,10
   sradi %r3,%r11,63
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r27
   sradi %r3,%r3,0
   bl record
   mr %r7,%r27
   bl check_alu
0: mr %r3,%r27
   sradi %r3,%r3,60
   bl record
   li %r7,-6
   bl check_alu
0: mr %r3,%r27
   sradi %r3,%r3,62
   bl record
   li %r7,-2
   bl check_alu_ca
0: mr %r3,%r27
   sradi %r3,%r3,63
   bl record
   li %r7,-1
   bl check_alu_ca

   # sradi.
0: li %r11,10
   sradi. %r3,%r11,0
   bl record
   li %r7,10
   bl check_alu_gt
0: li %r11,10
   sradi. %r3,%r11,2
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r11,10
   sradi. %r3,%r11,63
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r27
   sradi. %r3,%r3,0
   bl record
   mr %r7,%r27
   bl check_alu_lt
0: mr %r3,%r27
   sradi. %r3,%r3,60
   bl record
   li %r7,-6
   bl check_alu_lt
0: mr %r3,%r27
   sradi. %r3,%r3,62
   bl record
   li %r7,-2
   bl check_alu_ca_lt
0: mr %r3,%r27
   sradi. %r3,%r3,63
   bl record
   li %r7,-1
   bl check_alu_ca_lt

   # srawi
0: li %r11,10
   srawi %r3,%r11,0
   bl record
   li %r7,10
   bl check_alu
0: li %r11,10
   srawi %r3,%r11,2
   bl record
   li %r7,2
   bl check_alu
0: li %r11,10
   srawi %r3,%r11,31
   bl record
   li %r7,0
   bl check_alu
0: lis %r3,0xA000
   srawi %r3,%r3,0
   bl record
   lis %r7,0xA000
   bl check_alu
0: lis %r3,0xA000
   srawi %r3,%r3,28
   bl record
   li %r7,-6
   bl check_alu
0: lis %r3,0xA000
   srawi %r3,%r3,30
   bl record
   li %r7,-2
   bl check_alu_ca
0: lis %r3,0xA000
   srawi %r3,%r3,31
   bl record
   li %r7,-1
   bl check_alu_ca

   # srawi.
0: li %r11,10
   srawi. %r3,%r11,0
   bl record
   li %r7,10
   bl check_alu_gt
0: li %r11,10
   srawi. %r3,%r11,2
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r11,10
   srawi. %r3,%r11,31
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r3,0xA000
   srawi. %r3,%r3,0
   bl record
   lis %r7,0xA000
   bl check_alu_lt
0: lis %r3,0xA000
   srawi. %r3,%r3,28
   bl record
   li %r7,-6
   bl check_alu_lt
0: lis %r3,0xA000
   srawi. %r3,%r3,30
   bl record
   li %r7,-2
   bl check_alu_ca_lt
0: lis %r3,0xA000
   srawi. %r3,%r3,31
   bl record
   li %r7,-1
   bl check_alu_ca_lt

   ########################################################################
   # 3.3.12.2 Fixed-Point Rotate and Shift Instructions - srad, sraw
   ########################################################################

   # srad
0: li %r11,10
   li %r0,0
   srad %r3,%r11,%r0
   bl record
   li %r7,10
   bl check_alu
0: li %r11,10
   li %r7,2
   srad %r3,%r11,%r7
   bl record
   li %r7,2
   bl check_alu
0: li %r11,10
   li %r8,64
   srad %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu
0: mr %r3,%r27
   li %r0,0
   srad %r3,%r3,%r0
   bl record
   mr %r7,%r27
   bl check_alu
0: mr %r3,%r27
   li %r7,60
   srad %r3,%r3,%r7
   bl record
   li %r7,-6
   bl check_alu
0: mr %r7,%r27
   li %r8,62
   srad %r3,%r7,%r8
   bl record
   li %r7,-2
   bl check_alu_ca
0: mr %r3,%r27
   li %r8,64
   srad %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu_ca
0: mr %r3,%r27
   li %r9,127
   srad %r3,%r3,%r9
   bl record
   li %r7,-1
   bl check_alu_ca
0: mr %r3,%r27
   li %r11,128
   srad %r3,%r3,%r11
   bl record
   mr %r7,%r27
   bl check_alu

   # srad.
0: li %r11,10
   li %r0,0
   srad. %r3,%r11,%r0
   bl record
   li %r7,10
   bl check_alu_gt
0: li %r11,10
   li %r7,2
   srad. %r3,%r11,%r7
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r11,10
   li %r8,64
   srad. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: mr %r3,%r27
   li %r0,0
   srad. %r3,%r3,%r0
   bl record
   mr %r7,%r27
   bl check_alu_lt
0: mr %r3,%r27
   li %r7,60
   srad. %r3,%r3,%r7
   bl record
   li %r7,-6
   bl check_alu_lt
0: mr %r7,%r27
   li %r8,62
   srad. %r3,%r7,%r8
   bl record
   li %r7,-2
   bl check_alu_ca_lt
0: mr %r3,%r27
   li %r8,64
   srad. %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu_ca_lt
0: mr %r3,%r27
   li %r9,127
   srad. %r3,%r3,%r9
   bl record
   li %r7,-1
   bl check_alu_ca_lt
0: mr %r3,%r27
   li %r11,128
   srad. %r3,%r3,%r11
   bl record
   mr %r7,%r27
   bl check_alu_lt

   # sraw
0: li %r11,10
   li %r0,0
   sraw %r3,%r11,%r0
   bl record
   li %r7,10
   bl check_alu
0: li %r11,10
   li %r7,2
   sraw %r3,%r11,%r7
   bl record
   li %r7,2
   bl check_alu
0: li %r11,10
   li %r8,32
   sraw %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu
0: lis %r3,0xA000
   li %r0,0
   sraw %r3,%r3,%r0
   bl record
   lis %r7,0xA000
   bl check_alu
0: lis %r3,0xA000
   li %r7,28
   sraw %r3,%r3,%r7
   bl record
   li %r7,-6
   bl check_alu
0: lis %r7,0xA000
   li %r8,30
   sraw %r3,%r7,%r8
   bl record
   li %r7,-2
   bl check_alu_ca
0: lis %r3,0xA000
   li %r8,32
   sraw %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu_ca
0: lis %r3,0xA000
   li %r9,63
   sraw %r3,%r3,%r9
   bl record
   li %r7,-1
   bl check_alu_ca
0: lis %r3,0xA000
   li %r11,64
   sraw %r3,%r3,%r11
   bl record
   lis %r7,0xA000
   bl check_alu

   # sraw.
0: li %r11,10
   li %r0,0
   sraw. %r3,%r11,%r0
   bl record
   li %r7,10
   bl check_alu_gt
0: li %r11,10
   li %r7,2
   sraw. %r3,%r11,%r7
   bl record
   li %r7,2
   bl check_alu_gt
0: li %r11,10
   li %r8,32
   sraw. %r3,%r11,%r8
   bl record
   li %r7,0
   bl check_alu_eq
0: lis %r3,0xA000
   li %r0,0
   sraw. %r3,%r3,%r0
   bl record
   lis %r7,0xA000
   bl check_alu_lt
0: lis %r3,0xA000
   li %r7,28
   sraw. %r3,%r3,%r7
   bl record
   li %r7,-6
   bl check_alu_lt
0: lis %r7,0xA000
   li %r8,30
   sraw. %r3,%r7,%r8
   bl record
   li %r7,-2
   bl check_alu_ca_lt
0: lis %r3,0xA000
   li %r8,32
   sraw. %r3,%r3,%r8
   bl record
   li %r7,-1
   bl check_alu_ca_lt
0: lis %r3,0xA000
   li %r9,63
   sraw. %r3,%r3,%r9
   bl record
   li %r7,-1
   bl check_alu_ca_lt
0: lis %r3,0xA000
   li %r11,64
   sraw. %r3,%r3,%r11
   bl record
   lis %r7,0xA000
   bl check_alu_lt

   ########################################################################
   # 3.3.13 Move To/From System Register Instructions - mfvrsave, mtvrsave
   ########################################################################

   # mfvrsave/mtvrsave
0: li %r3,0
   mtvrsave %r3
   bl record
   li %r3,-1
   mfvrsave %r3
   li %r7,0
   cmpd %r3,%r7
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
   # Make sure the high 32 bits are ignored on write and cleared on read.
0: li %r3,-1
   mtvrsave %r3
   mfvrsave %r3
   bl record
   li %r7,0
   oris %r7,%r7,0xFFFF
   ori %r7,%r7,0xFFFF
   cmpd %r3,%r7
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6 Floating-Point Processor Instructions
   ########################################################################

   # Set up %r30 and %r31 with pointers to single- resp. double-precision
   # floating-point constant tables, since we can't use immediate values in
   # floating-point instructions or move directly between general-purpose
   # registers and floating-point registers.

0: bl 1f
1: mflr %r3
   addi %r30,%r3,2f-1b
   addi %r31,%r3,3f-1b
   b 0f
2: .int 0x00000000              #   0(%r30): 0.0f
   .int 0x3F800000              #   4(%r30): 1.0f
   .int 0x3FB504F3              #   8(%r30): sqrtf(2.0f)
   .int 0x00800000              #  12(%r30): minimum single-precision normal
   .balign 8
3: .int 0x00000000,0x00000000   #   0(%r31): 0.0
   .int 0x3FF00000,0x00000000   #   8(%r31): 1.0
   .int 0x7FF00000,0x00000000   #  16(%r31): inf
   .int 0xFFF00000,0x00000000   #  24(%r31): -inf
   .int 0x7FFA0000,0x00000000   #  32(%r31): QNaN
   .int 0xFFF40000,0x00000000   #  40(%r31): SNaN
   .int 0xFFFC0000,0x00000000   #  48(%r31): SNaN converted to QNaN
   .int 0x3FD00000,0x00000000   #  56(%r31): 0.25
   .int 0x3FE00000,0x00000000   #  64(%r31): 0.5
   .int 0x40000000,0x00000000   #  72(%r31): 2.0
   .int 0x41500000,0x00000000   #  80(%r31): 4194304.0
   .int 0x41500000,0x08000000   #  88(%r31): 4194304.125
   .int 0x41500000,0x10000000   #  96(%r31): 4194304.25
   .int 0x41500000,0x18000000   # 104(%r31): 4194304.375
   .int 0x41500000,0x20000000   # 112(%r31): 4194304.5
   .int 0x41500000,0x30000000   # 120(%r31): 4194304.75
   .int 0x41500000,0x40000000   # 128(%r31): 4194305.0
   .int 0x36A00000,0x00000000   # 136(%r31): Single-precision minimum denormal
   .int 0x36800000,0x00000000   # 144(%r31): Single-prec. minimum denormal / 4
   .int 0x47EFFFFF,0xE0000000   # 152(%r31): HUGE_VALF (maximum normal float)
   .int 0x47EFFFFF,0xE8000000   # 160(%r31): HUGE_VALF + epsilon/4
   .int 0x7FF80000,0x00000000   # 168(%r31): QNaN from invalid operations
   .int 0x40A00000,0x00000000   # 176(%r31): 2048.0
   .int 0x41400000,0x00000000   # 184(%r31): 2097152.0
   .int 0x41400000,0x08000000   # 192(%r31): 2097152.0625
   .int 0x414FFFFF,0xE0000000   # 200(%r31): 4194303.75 (exact in single-prec)
   .int 0x41E00000,0x00000000   # 208(%r31): (double) 2^31
   .int 0xC1E00000,0x00200000   # 216(%r31): (double) -(2^31+1)
   .int 0x43E00000,0x00000000   # 224(%r31): (double) 2^63
   .int 0xC3E00000,0x00000001   # 232(%r31): (double) -(2^63+2^11)
   .int 0x00100000,0x00000000   # 240(%r31): Double-precision minimum normal
   .int 0x00080000,0x00000000   # 248(%r31): Double-prec. minimum normal / 2
   .int 0x3FDFE000,0x00000000   # 256(%r31): 0.5 * 255/256 (fres bound)
   .int 0x3FE01000,0x00000000   # 264(%r31): 0.5 * 257/256 (fres bound)
   .int 0x3FFF0000,0x00000000   # 272(%r31): 2.0 * 31/32 (frsqrte bound)
   .int 0x40008000,0x00000000   # 280(%r31): 2.0 * 33/32 (frsqrte bound)
   .int 0x3FF55555,0x55555555   # 288(%r31): 1.333...
   .int 0x3FF80000,0x00000000   # 296(%r31): 1.5
   .int 0x3FFFFFFF,0xFFFFFFFF   # 304(%r31): 2.0 - 1ulp
   .int 0x3CA00000,0x00000000   # 312(%r31): 2.0 - (1.333... * 1.5)
   .int 0x7FEFFFFF,0xFFFFFFFF   # 320(%r31): HUGE_VAL (maximum normal double)
   .int 0x47E00000,0x00000000   # 328(%r31): (double)2^127
   .int 0x47F00000,0x00000000   # 336(%r31): (double)2^128 (out of float range)
   .int 0x46700000,0x00000000   # 344(%r31): (double)2^128 - HUGE_VALF
   .int 0x3CB00000,0x00000000   # 352(%r31): 2.0 - (2.0 - 1ulp)
   .int 0x00000000,0x00000001   # 360(%r31): minimum double-precision denormal

   ########################################################################
   # 4.6.2 Floating-Point Load Instructions
   ########################################################################

   # lfs
0: lfs %f0,4(%r30)
   bl record
   fcmpu cr0,%f0,%f1
   beq 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32
   # Verify that we can load a different value, in case lfs is broken but
   # F0 happened to contain 1.0 on entry.
0: lfs %f0,0(%r30)
   bl record
   fcmpu cr0,%f0,%f1
   bne 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32

   # lfsx
0: addi %r7,%r30,8
   li %r8,-4
   lfs %f0,0(%r30)
   lfsx %f0,%r7,%r8
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r8,%r30,8
   cmpd %r7,%r8
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: addi %r7,%r30,4
   li %r0,4
   lfs %f0,0(%r30)
   lfsx %f0,0,%r7
   bl record
   fcmpu cr0,%f0,%f1
   beq 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32

   # lfsu
0: addi %r7,%r30,8
   lfsu %f0,-4(%r7)
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r0,%r30,4
   cmpd %r7,%r0
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lfsux
0: addi %r7,%r30,8
   li %r0,-4
   lfs %f0,0(%r30)
   lfsux %f0,%r7,%r0
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r0,%r30,4
   cmpd %r7,%r0
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lfd
0: lfd %f0,0(%r31)
   bl record
   fcmpu cr0,%f0,%f1
   bne 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32
0: lfd %f0,8(%r31)
   bl record
   fcmpu cr0,%f0,%f1
   beq 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32

   # lfdx
0: addi %r7,%r31,16
   li %r8,-8
   lfd %f0,0(%r31)
   lfdx %f0,%r7,%r8
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r8,%r31,16
   cmpd %r7,%r8
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: addi %r7,%r31,8
   li %r0,8
   lfd %f0,0(%r31)
   lfdx %f0,0,%r7
   bl record
   fcmpu cr0,%f0,%f1
   beq 0f
   stfd %f0,8(%r6)
   addi %r6,%r6,32

   # lfdu
0: addi %r7,%r31,16
   lfd %f0,0(%r31)
   lfdu %f0,-8(%r7)
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r0,%r31,8
   cmpd %r7,%r0
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # lfdux
0: addi %r7,%r31,16
   li %r0,-8
   lfd %f0,0(%r31)
   lfdux %f0,%r7,%r0
   bl record
   fcmpu cr0,%f0,%f1
   bne 1f
   addi %r0,%r31,8
   cmpd %r7,%r0
   beq 0f
1: stfd %f0,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6.3 Floating-Point Store Instructions
   ########################################################################

0: li %r0,0
   std %r0,0(%r4)
   std %r0,8(%r4)

   # stfs
0: addi %r7,%r4,4
   stw %r0,0(%r4)
   stfs %f1,-4(%r7)
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x3F80
   cmpw %r3,%r8
   bne 1f
   addi %r8,%r4,4
   cmpd %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfsx
0: li %r8,-4
   stw %r0,0(%r4)
   stfsx %f1,%r7,%r8
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x3F80
   cmpw %r3,%r8
   bne 1f
   addi %r8,%r4,4
   cmpd %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,4
   stw %r0,0(%r4)
   stfsx %f1,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x3F80
   cmpw %r3,%r8
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # stfsu
0: stw %r0,0(%r4)
   stfsu %f1,-4(%r7)
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x3F80
   cmpw %r3,%r8
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfsux
0: addi %r7,%r4,4
   li %r8,-4
   stw %r0,0(%r4)
   stfsux %f1,%r7,%r8
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x3F80
   cmpw %r3,%r8
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfd
0: addi %r7,%r4,8
   std %r0,0(%r4)
   stfd %f1,-8(%r7)
   bl record
   ld %r3,0(%r4)
   lis %r8,0x3FF0
   sldi %r8,%r8,32
   cmpd %r3,%r8
   bne 1f
   addi %r8,%r4,8
   cmpd %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfdx
0: li %r8,-8
   std %r0,0(%r4)
   stfdx %f1,%r7,%r8
   bl record
   ld %r3,0(%r4)
   lis %r8,0x3FF0
   sldi %r8,%r8,32
   cmpd %r3,%r8
   bne 1f
   addi %r8,%r4,8
   cmpd %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,8
   std %r0,0(%r4)
   stfdx %f1,0,%r4
   bl record
   ld %r3,0(%r4)
   lis %r8,0x3FF0
   sldi %r8,%r8,32
   cmpd %r3,%r8
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # stfdu
0: std %r0,0(%r4)
   stfdu %f1,-8(%r7)
   bl record
   ld %r3,0(%r4)
   lis %r8,0x3FF0
   sldi %r8,%r8,32
   cmpd %r3,%r8
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfdux
0: addi %r7,%r4,8
   li %r8,-8
   std %r0,0(%r4)
   stfdux %f1,%r7,%r8
   bl record
   ld %r3,0(%r4)
   lis %r8,0x3FF0
   sldi %r8,%r8,32
   cmpd %r3,%r8
   bne 1f
   cmpd %r7,%r4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # stfiwx
0: lfd %f0,104(%r31)  # 4194304.375
   addi %r7,%r4,4
   li %r8,-4
   stw %r0,0(%r4)
   stfiwx %f0,%r7,%r8
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x1800
   cmpw %r3,%r8
   bne 1f
   addi %r8,%r4,4
   cmpd %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: li %r0,4
   stw %r0,0(%r4)
   stfiwx %f0,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r8,0x1800
   cmpw %r3,%r8
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # Loads and stores should not change the sign of zero.
0: lis %r7,0x8000
   stw %r7,0(%r4)
   li %r0,0
   stw %r0,4(%r4)
   lfs %f7,0(%r4)
   stw %r0,8(%r4)
   stfs %f7,8(%r4)
   bl record
   lwz %r3,8(%r4)
   cmpw %r3,%r7
   beq 0f
   stw %r3,8(%r6)
   addi %r6,%r6,32
0: lfd %f8,0(%r4)
   stw %r0,8(%r4)
   stw %r7,12(%r4)
   stfd %f8,8(%r4)
   bl record
   lwz %r3,8(%r4)
   lwz %r8,12(%r4)
   cmpw %r3,%r7
   bne 1f
   cmpwi %r8,0
   beq 0f
1: stw %r3,8(%r6)
   stw %r8,12(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6.8 Floating-Point Status and Control Register Instructions
   ########################################################################

   # mffs/mtfsf
0: lfd %f0,0(%r31)  # 0.0
   mtfsf 255,%f0
   lfd %f0,88(%r31)  # 4194304.125 (arbitary value with nonzero low word)
   mffs %f0
   bl record
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   cmpwi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,~0x0804  # Don't try to set bits 20 (reserved) or 29 (non-IEEE,
   stw %r0,4(%r4)  #    which is not implemented on the Cell).
   lfd %f0,0(%r4)
   mtfsf 255,%f0
   bl record
   lfd %f0,88(%r31)
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   cmpwi %r3,~0x0804
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,0
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf 8,%f0
   bl record
   lfd %f0,88(%r31)
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0xFFFF
   ori %r0,%r0,0x07FB
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
   # mtfsf should not alter bits 1-2 of FPSCR.
0: lis %r0,0x9000
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf 128,%f0
   bl record
   lfd %f0,88(%r31)
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0xFFFF
   ori %r0,%r0,0x07FB
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: lis %r0,0x6000
   stw %r0,4(%r4)
   lfd %f2,0(%r4)
   mtfsf 255,%f2
   bl record
   lfd %f0,88(%r31)
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   cmpwi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mffs.
0: li %r0,0
   mtcr %r0
   lis %r0,0x1234
   ori %r0,%r0,0x5678
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf 255,%f0
   mffs. %f0
   bl record
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r8
   lis %r9,0x0700   # FPSCR[1:2] were automatically set by mtfsf.
   cmpd %r8,%r9
   bne 1f
   lis %r0,0x7234
   ori %r0,%r0,0x5678
   cmpw %r3,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32

   # mcrfs
0: li %r0,0
   mtcr %r0
   lis %r0,0x123C
   ori %r0,%r0,0x5678
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf 255,%f0
   mcrfs cr7,0
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r8
   cmpdi %r8,7
   bne 1f
   lis %r0,0x623C
   ori %r0,%r0,0x5678
   cmpw %r3,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   mcrfs cr7,3
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r8
   cmpdi %r8,0xC
   bne 1f
   lis %r0,0x6234   # Non-exception bits are not cleared.
   ori %r0,%r0,0x5678
   cmpw %r3,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   mcrfs cr5,1
   mcrfs cr6,2
   mcrfs cr7,5
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r8
   cmpdi %r8,0x236
   bne 1f
   lis %r0,0x0004   # Clearing exception bits should clear FEX and VX too.
   ori %r0,%r0,0x5078
   cmpw %r3,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32

   # mtfsfi/mtfsfi.
0: li %r0,0
   mtcr %r0
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf 255,%f0
   mtfsfi. 0,1
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r7
   lis %r0,0x1000   # FPSCR[0] should not have been set.
   cmpw %r3,%r0
   bne 1f
   lis %r0,0x0100
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsfi 2,8
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0x3080   # FPSCR[2] should have been set along with FPSCR[8].
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtfsf.
0: li %r0,0
   mtcr %r0
   lis %r0,0x1234
   ori %r0,%r0,0x5678
   stw %r0,4(%r4)
   lfd %f0,0(%r4)
   mtfsf. 255,%f0
   bl record
   mfcr %r0
   lis %r3,0x0700
   cmpd %r0,%r3
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtfsb0
0: mtfsb0 28
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0x7234
   ori %r0,%r0,0x5670
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: mtfsb0 1         # Should have no effect.
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0x7234
   ori %r0,%r0,0x5670
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtfsb0.
0: li %r0,0
   mtcr %r0
   mtfsb0. 3        # Also clears bit 1.
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r7
   lis %r0,0x2234
   ori %r0,%r0,0x5670
   cmpw %r3,%r0
   bne 1f
   lis %r0,0x0200
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # mtfsb1
0: mtfsb1 16
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0x2234
   ori %r0,%r0,0xD670
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: mtfsb1 1         # Should have no effect.
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   lis %r0,0x2234
   ori %r0,%r0,0xD670
   cmpw %r3,%r0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtfsb1.
0: li %r0,0
   mtcr %r0
   mtfsb1. 3        # Also sets bits 0 and 1.
   bl record
   mffs %f0
   stfd %f0,0(%r4)
   lwz %r3,4(%r4)
   mfcr %r7
   lis %r0,0xF234
   ori %r0,%r0,0xD670
   cmpw %r3,%r0
   bne 1f
   lis %r0,0x0F00
   cmpd %r7,%r0
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6.4 Floating-Point Move Instructions
   ########################################################################

0: lfd %f0,0(%r31)  # 0.0
   lfd %f5,32(%r31) # QNaN
   lfd %f6,40(%r31) # SNaN
   mtfsf 255,%f0
   mtfsfi 0,8       # Ensure that Rc=1 insns have a nonzero value to write.
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r11,4(%r4)
   li %r0,0

   # fmr
0: mtcr %r0
   fmr %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3         # Also check that FPSCR is unmodified.
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x3FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0      # Check that CR1 is unmodified (Rc=0).
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
   # Check that NaNs don't cause exceptions with these instructions.
0: fmr %f3,%f5
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x7FFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fmr %f3,%f6
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xFFF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fmr.
0: mtcr %r0
   fmr. %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x3FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   lis %r7,0x0800
   cmpw %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fneg
0: mtcr %r0
   fneg %f2,%f1
   bl record
   std %r0,0(%r4)
   stfd %f2,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xBFF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fneg %f3,%f5
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xFFFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fneg %f3,%f6
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x7FF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
   # fneg should negate the sign of zero as well.
0: fneg %f3,%f0
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x8000
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fneg %f3,%f0
   fneg %f3,%f3
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   cmpdi %r3,0
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fneg.
0: mtcr %r0
   fneg. %f2,%f1
   bl record
   std %r0,0(%r4)
   stfd %f2,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xBFF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   lis %r7,0x0800
   cmpw %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fabs
0: mtcr %r0
   fmr %f3,%f0
   fabs %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x3FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fmr %f3,%f0
   fabs %f3,%f2
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x3FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fabs %f3,%f5
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x7FFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fabs %f3,%f6
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x7FF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fabs.
0: mtcr %r0
   fmr %f3,%f0
   fabs. %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0x3FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   lis %r7,0x0800
   cmpw %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fnabs
0: mtcr %r0
   fmr %f3,%f0
   fnabs %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xBFF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fmr %f3,%f0
   fnabs %f3,%f2
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xBFF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fnabs %f3,%f5
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xFFFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: fnabs %f3,%f6
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xFFF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   cmpwi %r3,0
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   # fnabs.
0: mtcr %r0
   fmr %f3,%f0
   fnabs. %f3,%f1
   bl record
   std %r0,0(%r4)
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   mffs %f3
   stfd %f3,8(%r4)
   lwz %r8,12(%r4)
   mfcr %r9
   lis %r7,0xBFF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpw %r8,%r11
   bne 1f
   andis. %r3,%r9,0x0F00
   lis %r7,0x0800
   cmpw %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6.7 Floating-Point Compare Instructions
   ########################################################################

0: li %r0,0
   mtcr %r0

   # fcmpu
0: mtfsf 255,%f0
   fcmpu cr0,%f0,%f0    # 0.0 == 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   lis %r8,0x2000
   cmpw %r3,%r8
   bne 1f
   cmpwi %r7,0x2000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: fcmpu cr1,%f1,%f0    # 1.0 > 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   lis %r8,0x2400
   cmpw %r3,%r8
   bne 1f
   cmpwi %r7,0x4000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpu cr7,%f2,%f0    # -1.0 < 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,8
   bne 1f
   ori %r8,%r0,0x8000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpu cr7,%f5,%f0    # QNaN ? 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   cmpwi %r7,0x1000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
   # Clear FPSCR here to verify that FPSCR[19] is set again and not just
   # carried over from the last test.
0: mtfsf 255,%f0
   mtcr %r0
   fcmpu cr7,%f0,%f5    # 0.0 ? QNaN
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   cmpwi %r7,0x1000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0
   mtcr %r0
   fcmpu cr7,%f6,%f0    # SNaN ? 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA100
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
   # Clear FPSCR to verify that FPSCR[19] is set and also to ensure that
   # the exception flag is newly raised.
0: mtfsf 255,%f0
   mtcr %r0
   fcmpu cr7,%f0,%f6    # 0.0 ? SNaN
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA100
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
   # Test again with FPSCR[FX] cleared to ensure that it's not set again
   # when the exception flag does not change.
0: mtfsb0 0
   mtcr %r0
   fcmpu cr5,%f0,%f6    # 0.0 ? SNaN (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x100
   bne 1f
   lis %r8,0x2100
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
   # Check that a set exception flag is not cleared if no exception occurs.
0: mtcr %r0
   fcmpu cr5,%f0,%f0    # 0.0 == 0.0 (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x200
   bne 1f
   lis %r8,0x2100
   ori %r8,%r8,0x2000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # fcmpo (VE=0)
0: mtcr %r0
   mtfsf 255,%f0
   fcmpo cr0,%f0,%f0    # 0.0 == 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   lis %r8,0x2000
   cmpw %r3,%r8
   bne 1f
   cmpwi %r7,0x2000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: fcmpo cr1,%f1,%f0    # 1.0 > 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   lis %r8,0x2400
   cmpw %r3,%r8
   bne 1f
   cmpwi %r7,0x4000
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpo cr7,%f2,%f0    # -1.0 < 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,8
   bne 1f
   ori %r8,%r0,0x8000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpo cr7,%f5,%f0    # QNaN ? 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA008
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0
   mtcr %r0
   fcmpo cr7,%f0,%f5    # 0.0 ? QNaN
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA008
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0
   mtcr %r0
   fcmpo cr7,%f6,%f0    # SNaN ? 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA108
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0
   mtcr %r0
   fcmpo cr7,%f0,%f6    # 0.0 ? SNaN
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,1
   bne 1f
   lis %r8,0xA108
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsb0 0
   mtcr %r0
   fcmpo cr5,%f0,%f6    # 0.0 ? SNaN (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x100
   bne 1f
   lis %r8,0x2108
   ori %r8,%r8,0x1000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpo cr5,%f0,%f0    # 0.0 == 0.0 (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x200
   bne 1f
   lis %r8,0x2108
   ori %r8,%r8,0x2000
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # fcmpo (VE=1)
0: mtfsf 255,%f0
   mtfsb1 24
   mtcr %r0
   fcmpo cr6,%f6,%f0    # SNaN ? 0.0
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x10
   bne 1f
   lis %r8,0xE100
   ori %r8,%r8,0x1080
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0
   mtfsb1 24
   mtcr %r0
   fcmpo cr6,%f0,%f6    # 0.0 ? SNaN
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x10
   bne 1f
   lis %r8,0xE100
   ori %r8,%r8,0x1080
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtfsb0 0
   mtcr %r0
   fcmpo cr4,%f0,%f6    # 0.0 ? SNaN (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x1000
   bne 1f
   lis %r8,0x6100
   ori %r8,%r8,0x1080
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32
0: mtcr %r0
   fcmpo cr4,%f0,%f0    # 0.0 == 0.0 (2nd time)
   bl record
   mfcr %r3
   mffs %f3
   stfd %f3,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0x2000
   bne 1f
   lis %r8,0x6100
   ori %r8,%r8,0x2080
   cmpw %r7,%r8
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   ########################################################################
   # 4.6.3 Floating-Point Store Instructions - float/double conversion
   ########################################################################

   # Check for two possible bugs in software implementations:
   # - Conversion between single and double precision causes an exception
   #   which terminates the program.
   # - Conversion leaves a stale exception flag which is picked up by a
   #   subsequent floating-point operation.
   # We assume here that frsp(0.0) works and use it as a method of
   # catching stale exceptions; frsp is fully tested below.

0: li %r0,0
   mtcr %r0
   mtfsf 255,%f0

   # lfs (denormal)
0: li %r3,1
   stw %r3,0(%r4)
   lfs %f3,0(%r4)
   bl record
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x36A0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0  # Make sure any stale exceptions don't break the next test.
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0  # Round-to-single-precision of 0.0 should cause no exceptions.
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfs (infinity)
0: lis %r3,0x7F80
   stw %r3,0(%r4)
   lfs %f6,0(%r4)
   bl record
   stfd %f6,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfs (QNaN)
0: lis %r3,0x7FD0
   stw %r3,0(%r4)
   lfs %f7,0(%r4)
   bl record
   stfd %f7,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfs (SNaN)
0: lis %r3,0x7FA0
   stw %r3,0(%r4)
   lfs %f8,0(%r4)
   bl record
   stfd %f8,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfsx (denormal)
0: li %r3,1
   stw %r3,0(%r4)
   lfsx %f3,0,%r4
   bl record
   stfd %f3,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x36A0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfsx (infinity)
0: lis %r3,0x7F80
   stw %r3,0(%r4)
   lfsx %f6,0,%r4
   bl record
   stfd %f6,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FF0
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfsx (QNaN)
0: lis %r3,0x7FD0
   stw %r3,0(%r4)
   lfsx %f7,0,%r4
   bl record
   stfd %f7,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FFA
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # lfsx (SNaN)
0: lis %r3,0x7FA0
   stw %r3,0(%r4)
   lfsx %f8,0,%r4
   bl record
   stfd %f8,0(%r4)
   ld %r3,0(%r4)
   lis %r7,0x7FF4
   sldi %r7,%r7,32
   cmpd %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (denormal)
0: lis %r3,0x36A0
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f3,0(%r4)
   stfs %f3,0(%r4)
   bl record
   lwz %r3,0(%r4)
   li %r7,1
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (infinity)
0: lis %r3,0x7FF0
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f6,0(%r4)
   stfs %f6,0(%r4)
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7F80
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (QNaN)
0: lis %r3,0x7FFA
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f7,0(%r4)
   stfs %f7,0(%r4)
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7FD0
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (QNaN)
0: lis %r3,0x7FF4
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f8,0(%r4)
   stfs %f8,0(%r4)
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7FA0
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (denormal)
0: lis %r3,0x36A0
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f3,0(%r4)
   stfsx %f3,0,%r4
   bl record
   lwz %r3,0(%r4)
   li %r7,1
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (infinity)
0: lis %r3,0x7FF0
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f6,0(%r4)
   stfsx %f6,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7F80
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (QNaN)
0: lis %r3,0x7FFA
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f7,0(%r4)
   stfsx %f7,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7FD0
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   # stfs (QNaN)
0: lis %r3,0x7FF4
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %f8,0(%r4)
   stfsx %f8,0,%r4
   bl record
   lwz %r3,0(%r4)
   lis %r7,0x7FA0
   cmpw %r3,%r7
   beq 1f
   std %r3,8(%r6)
   li %r3,-1
   std %r3,16(%r6)
   addi %r6,%r6,32
   frsp %f3,%f0
   mtfsf 255,%f0
   b 0f
1: frsp %f3,%f0
   fmr %f4,%f0
   bl check_fpu_pzero

   ########################################################################
   # 4.6.6 Floating-Point Rounding and Conversion Instructions - frsp
   # (and general rounding tests)
   ########################################################################

   # Preload floating-point constants for convenience in subsequent tests.
0: lfd %f24,80(%r31)   # 4194304.0
   lfd %f25,88(%r31)   # 4194304.125
   lfd %f26,96(%r31)   # 4194304.25
   lfd %f27,104(%r31)  # 4194304.375
   lfd %f28,112(%r31)  # 4194304.5
   lfd %f29,120(%r31)  # 4194304.75
   lfd %f30,128(%r31)  # 4194305.0
   lfd %f5,136(%r31)   # Single-precision minimum denormal
   lfd %f6,144(%r31)   # Single-precision minimum denormal / 4
   lfd %f7,152(%r31)   # HUGE_VALF (maximum normal single-precision value)
   lfd %f8,160(%r31)   # HUGE_VALF + epsilon/4
   lfd %f9,16(%r31)    # Positive infinity
   lfd %f10,32(%r31)   # QNaN
   lfd %f11,40(%r31)   # SNaN
   lfd %f12,48(%r31)   # SNaN converted to QNaN

   # frsp (RN = round to nearest)
0: frsp %f3,%f24    # 4194304.0 (exact)
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: frsp %f3,%f25    # 4194304.125 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f26    # 4194304.25 (round to even)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f27    # 4194304.375 (round up)
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm_inex
0: frsp %f3,%f28    # 4194304.5 (exact)
   bl record
   bl check_fpu_pnorm
0: frsp %f3,%f29    # 4194304.75 (round to even)
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm_inex
0: frsp %f3,%f30    # 4194305.0 (exact)
   bl record
   bl check_fpu_pnorm
0: frsp %f3,%f5     # Single-precision minimum denormal (exact)
   bl record
   fmr %f4,%f5
   bl check_fpu_pdenorm
0: frsp %f3,%f6     # Single-precision minimum denormal / 4 (round down)
   bl record
   fmr %f4,%f0
   bl add_fpscr_ux
   bl check_fpu_pzero_inex
0: fneg %f3,%f6     # -(Single-precision minimum denormal / 4) (round up)
   frsp %f3,%f3
   bl record
   bl add_fpscr_ux
   bl check_fpu_nzero_inex
0: frsp %f3,%f7     # HUGE_VALF (exact)
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: frsp %f3,%f8     # HUGE_VALF + epsilon/4 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: fneg %f4,%f8     # -(HUGE_VALF + epsilon/4) (round up)
   frsp %f3,%f4
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm_inex
0: frsp %f3,%f9     # Positive infinity (exact)
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: frsp %f3,%f10    # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: frsp %f3,%f11    # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

   # frsp (RN = round toward zero)
0: mtfsfi 7,1
   frsp %f3,%f24    # 4194304.0 (exact)
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: frsp %f3,%f25    # 4194304.125 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f26    # 4194304.25 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f27    # 4194304.375 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f28    # 4194304.5 (exact)
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm
0: frsp %f3,%f29    # 4194304.75 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f30    # 4194305.0 (exact)
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm
0: frsp %f3,%f5     # Single-precision minimum denormal (exact)
   bl record
   fmr %f4,%f5
   bl check_fpu_pdenorm
0: frsp %f3,%f6     # Single-precision minimum denormal / 4 (round down)
   bl record
   fmr %f4,%f0
   bl add_fpscr_ux
   bl check_fpu_pzero_inex
0: fneg %f3,%f6     # -(Single-precision minimum denormal / 4) (round up)
   frsp %f3,%f3
   bl record
   bl add_fpscr_ux
   bl check_fpu_nzero_inex
0: frsp %f3,%f7     # HUGE_VALF (exact)
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: frsp %f3,%f8     # HUGE_VALF + epsilon/4 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: fneg %f4,%f8     # -(HUGE_VALF + epsilon/4) (round up)
   frsp %f3,%f4
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm_inex
0: frsp %f3,%f9     # Positive infinity (exact)
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: frsp %f3,%f10    # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: frsp %f3,%f11    # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

   # frsp (RN = round toward +infinity)
0: mtfsfi 7,2
   frsp %f3,%f24    # 4194304.0 (exact)
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: frsp %f3,%f25    # 4194304.125 (round up)
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm_inex
0: frsp %f3,%f26    # 4194304.25 (round up)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f27    # 4194304.375 (round up)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f28    # 4194304.5 (exact)
   bl record
   bl check_fpu_pnorm
0: frsp %f3,%f29    # 4194304.75 (round up)
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm_inex
0: frsp %f3,%f30    # 4194305.0 (exact)
   bl record
   bl check_fpu_pnorm
0: frsp %f3,%f5     # Single-precision minimum denormal (exact)
   bl record
   fmr %f4,%f5
   bl check_fpu_pdenorm
0: frsp %f3,%f6     # Single-precision minimum denormal / 4 (round up)
   bl record
   bl add_fpscr_ux
   bl check_fpu_pdenorm_inex
0: fneg %f3,%f6     # -(Single-precision minimum denormal / 4) (round up)
   frsp %f3,%f3
   bl record
   bl add_fpscr_ux
   fmr %f4,%f0
   bl check_fpu_nzero_inex
0: frsp %f3,%f7     # HUGE_VALF (exact)
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: frsp %f3,%f8     # HUGE_VALF + epsilon/4 (round up)
   bl record
   fmr %f4,%f9
   bl add_fpscr_ox
   bl check_fpu_pinf_inex
0: fneg %f4,%f8     # -(HUGE_VALF + epsilon/4) (round up)
   frsp %f3,%f4
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm_inex
0: frsp %f3,%f9     # Positive infinity (exact)
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: frsp %f3,%f10    # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: frsp %f3,%f11    # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

   # frsp (RN = round toward -infinity)
0: mtfsfi 7,3
   frsp %f3,%f24    # 4194304.0 (exact)
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: frsp %f3,%f25    # 4194304.125 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f26    # 4194304.25 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f27    # 4194304.375 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f28    # 4194304.5 (exact)
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm
0: frsp %f3,%f29    # 4194304.75 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: frsp %f3,%f30    # 4194305.0 (exact)
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm
0: frsp %f3,%f5     # Single-precision minimum denormal (exact)
   bl record
   fmr %f4,%f5
   bl check_fpu_pdenorm
0: frsp %f3,%f6     # Single-precision minimum denormal / 4 (round down)
   bl record
   fmr %f4,%f0
   bl add_fpscr_ux
   bl check_fpu_pzero_inex
0: fneg %f3,%f6     # -(Single-precision minimum denormal / 4) (round down)
   frsp %f3,%f3
   bl record
   fneg %f4,%f5
   bl add_fpscr_ux
   bl check_fpu_ndenorm_inex
0: frsp %f3,%f7     # HUGE_VALF (exact)
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: frsp %f3,%f8     # HUGE_VALF + epsilon/4 (round down)
   bl record
   bl check_fpu_pnorm_inex
0: fneg %f4,%f8     # -(HUGE_VALF + epsilon/4) (round down)
   frsp %f3,%f4
   bl record
   fneg %f4,%f9
   bl add_fpscr_ox
   bl check_fpu_ninf_inex
0: frsp %f3,%f9     # Positive infinity (exact)
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: frsp %f3,%f10    # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: frsp %f3,%f11    # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

   # frsp (SNaN and VE=1)
0: mtfsf 255,%f0
   mtfsb1 24
   fmr %f4,%f24
   frsp %f4,%f11  # Should not change the target register's contents.
   bl record
   fmr %f3,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24

   # frsp (FPSCR[FX] handling)
0: frsp %f4,%f11
   mtfsb0 0
   frsp %f4,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # frsp (exception persistence)
0: frsp %f4,%f11
   frsp %f4,%f24
   bl record
   fmr %f3,%f4
   fmr %f4,%f24
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: fix frsp.
.if 0
   # frsp.
   # We assume frsp and frsp. share the same implementation and just check
   # that CR1 is updated properly (and likewise in tests below).
0: frsp. %f3,%f11   # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0    # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   frsp. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11     # Register contents should be unchanged.
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif
   ########################################################################
   # 4.6.5.1 Floating-Point Elementary Arithmetic Instructions
   ########################################################################

   # Swap out some constants.
0: lfd %f2,72(%r31)    # 2.0
   lfd %f28,184(%r31)  # 2097152.0
   lfd %f29,192(%r31)  # 2097152.0625

   # fadd
0: fadd %f3,%f1,%f24    # normal + normal
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm
0: fadd %f3,%f9,%f1     # +infinity + normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fadd %f3,%f9,%f9     # +infinity + +infinity
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9        # +infinity + -infinity
   fadd %f3,%f9,%f13
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: fadd %f3,%f10,%f1    # QNaN + normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fadd %f3,%f1,%f11    # normal + SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fadd %f3,%f11,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # -infinity + +infinity (exception enabled)
   mtfsb1 24
   fneg %f13,%f9
   fmr %f3,%f24
   fadd %f3,%f13,%f9
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24

   # fadd (FPSCR[FX] handling)
0: fadd %f4,%f1,%f11
   mtfsb0 0
   fadd %f4,%f1,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fadd (exception persistence)
0: fadd %f4,%f1,%f11
   fadd %f4,%f1,%f24
   bl record
   fmr %f3,%f4
   fmr %f4,%f30
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
   # fadd.
.if 0
0: fadd. %f3,%f1,%f11   # normal + SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # normal + SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fadd. %f3,%f1,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fadds
0: fadds %f3,%f1,%f25   # normal + normal
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm_inex
   # Check rounding of input values.
0: mtfsfi 7,1           # 1.999...9 + 0.000...1 (round down)
   lfd %f3,304(%r31)
   lfd %f4,352(%r31)
   fadds %f3,%f3,%f4    # Input values are not truncated.
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: mtfsfi 7,1           # 0.000...1 + 1.999...9 (round down)
   lfd %f3,304(%r31)
   lfd %f4,352(%r31)
   fadds %f3,%f4,%f3
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
   # The Cell gets confused if given an input value outside the range of a
   # single-precision value and just returns NaN with no exception flags
   # set, even if the final result would be within single-precision range.
0: lfd %f4,336(%r31)    # 2^128 + -HUGE_VALF
   fneg %f13,%f7
   fadds %f3,%f4,%f13
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # -HUGE_VALF + 2^128
   fneg %f13,%f7
   fadds %f3,%f13,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # 2^128 + SNaN
   fadds %f3,%f4,%f11
   bl record
   fmr %r4,%f12         # SNaNs takes precedence over out-of-range values.
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # SNaN + 2^128
   fadds %f3,%f11,%f4
   bl record
   fmr %r4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fadds.
0: fadds. %f3,%f1,%f11  # normal + SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fsub
0: fsub %f3,%f30,%f1    # normal - normal
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: fsub %f3,%f9,%f1     # +infinity - normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fsub %f3,%f9,%f9     # +infinity - +infinity
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: fneg %f13,%f9        # +infinity - -infinity
   fsub %f3,%f9,%f13
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fsub %f3,%f10,%f1    # QNaN - normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fsub %f3,%f1,%f11    # normal - SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fsub %f3,%f11,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # -infinity - -infinity (exception enabled)
   mtfsb1 24
   fneg %f13,%f9
   fmr %f3,%f24
   fsub %f3,%f13,%f13
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24

   # fsub (FPSCR[FX] handling)
0: fsub %f4,%f1,%f11
   mtfsb0 0
   fsub %f4,%f1,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fsub (exception persistence)
0: fsub %f4,%f1,%f11
   fsub %f4,%f30,%f1
   bl record
   fmr %f3,%f4
   fmr %f4,%f24
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fsub.
0: fsub. %f3,%f1,%f11   # normal - SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # normal - SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fsub. %f3,%f1,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fsubs
0: lfd %f13,56(%r31)    # normal - normal
   fsubs %f3,%f27,%f13
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm_inex
0: mtfsfi 7,1           # 1.999...9 - -0.000...1 (round down)
   lfd %f3,304(%r31)
   lfd %f4,352(%r31)
   fneg %f4,%f4
   fsubs %f3,%f3,%f4
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: mtfsfi 7,1           # 0.000...1 - -1.999...9 (round down)
   lfd %f3,304(%r31)
   fneg %f3,%f3
   lfd %f4,352(%r31)
   fsubs %f3,%f4,%f3
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: lfd %f4,336(%r31)    # 2^128 - HUGE_VALF
   fsubs %f3,%f4,%f7
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # HUGE_VALF - 2^128
   fsubs %f3,%f7,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # 2^128 - SNaN
   fsubs %f3,%f4,%f11
   bl record
   fmr %r4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # SNaN - 2^128
   fsubs %f3,%f11,%f4
   bl record
   fmr %r4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fsubs.
0: fsubs. %f3,%f1,%f11  # normal - SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fmul
0: fmul %f3,%f2,%f28    # normal * normal
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: fmul %f3,%f0,%f28    # 0 * normal
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fneg %f4,%f0         # -0 * normal
   fmul %f3,%f4,%f28
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f28        # 0 * -normal
   fmul %f3,%f0,%f4
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fmul %f3,%f9,%f2     # +infinity * normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fmul %f3,%f9,%f9     # +infinity * +infinity
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9        # +infinity * -infinity
   fmul %f3,%f9,%f13
   bl record
   fmr %f4,%f13
   bl check_fpu_ninf
0: fmul %f3,%f9,%f0     # +infinity * 0
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f13,%f9        # 0 * -infinity
   fmul %f3,%f0,%f13
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fmul %f3,%f10,%f1    # QNaN * normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fmul %f3,%f1,%f11    # normal * SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN * normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmul %f3,%f11,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # 0 * +infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmul %f3,%f0,%f9
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vximz
   bl check_fpu_noresult
   mtfsb0 24

   # fmul (FPSCR[FX] handling)
0: fmul %f4,%f1,%f11
   mtfsb0 0
   fmul %f4,%f1,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fmul (exception persistence)
0: fmul %f4,%f1,%f11
   fmul %f4,%f2,%f28
   bl record
   fmr %f3,%f4
   fmr %f4,%f24
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fmul.
0: fmul. %f3,%f1,%f11   # normal * SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # normal * SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fmul. %f3,%f1,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fmuls
0: fmuls %f3,%f2,%f29   # normal * normal
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm_inex
0: fneg %f4,%f0         # -0 * normal
   fmuls %f3,%f4,%f28
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f28        # 0 * -normal
   fmuls %f3,%f0,%f4
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: mtfsfi 7,2           # 1.333... * 1.5 (round up)
   lfd %f3,288(%r31)
   lfd %f4,296(%r31)
   fmuls %f3,%f3,%f4
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm_inex
   mtfsfi 7,0
0: mtfsfi 7,1           # 1.333...4 * 1.5 (round down)
   ld %r3,288(%r31)
   addi %r3,%r3,1
   std %r3,0(%r4)
   lfd %f3,0(%r4)
   lfd %f13,296(%r31)
   fmuls %f3,%f3,%f13
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm_inex
   mtfsfi 7,0
0: mtfsfi 7,2           # 1.5 * 1.333... (round up)
   lfd %f3,288(%r31)
   lfd %f4,296(%r31)
   fmuls %f3,%f4,%f3
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm_inex
   mtfsfi 7,0
0: mtfsfi 7,1           # 1.5 * 1.333...4 (round down)
   ld %r3,288(%r31)
   addi %r3,%r3,1
   std %r3,0(%r4)
   lfd %f3,0(%r4)
   lfd %f13,296(%r31)
   fmuls %f3,%f13,%f3
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm_inex
   mtfsfi 7,0
0: lfd %f4,336(%r31)    # 2^128 * 0
   fmuls %f3,%f4,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # 0 * 2^128
   fmuls %f3,%f0,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # 2^128 * SNaN
   fmuls %f3,%f4,%f11
   bl record
   fmr %r4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: lfd %f4,336(%r31)    # SNaN * 2^128
   fmuls %f3,%f11,%f4
   bl record
   fmr %r4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fmuls.
0: fmuls. %f3,%f1,%f11  # normal * SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fdiv
0: fdiv %f3,%f24,%f2    # normal / normal
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm
0: fdiv %f3,%f9,%f2     # +infinity / normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fdiv %f3,%f9,%f9     # +infinity / +infinity
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxidi
   bl check_fpu_nan
0: fdiv %f3,%f2,%f0     # normal / 0
   bl record
   fmr %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_pinf
0: fneg %f3,%f0         # normal / -0
   fdiv %f3,%f2,%f3
   bl record
   fneg %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_ninf
0: fdiv %f3,%f0,%f0     # 0 / 0
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxzdz
   bl check_fpu_nan
0: fdiv %f3,%f10,%f1    # QNaN / normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fdiv %f3,%f1,%f11    # normal / SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN / normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fdiv %f3,%f11,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # +infinity / -infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fneg %f13,%f9
   fdiv %f3,%f9,%f13
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxidi
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # 0 / 0 (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmr %f4,%f0
   fdiv %f3,%f4,%f4
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxzdz
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsb1 27            # normal / 0 (exception enabled)
   fmr %f3,%f24
   fdiv %f3,%f1,%f0
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_zx
   bl check_fpu_noresult
   mtfsb0 27

   # fdiv (FPSCR[FX] handling)
0: fdiv %f4,%f1,%f11
   mtfsb0 0
   fdiv %f4,%f1,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fdiv (exception persistence)
0: fdiv %f4,%f1,%f11
   fdiv %f4,%f24,%f2
   bl record
   fmr %f3,%f4
   fmr %f4,%f28
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fdiv.
0: fdiv. %f3,%f1,%f11   # normal / SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # normal / SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fdiv. %f3,%f1,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fdivs
0: fdivs %f3,%f25,%f2  # normal / normal
   bl record
   fmr %f4,%f28
   bl check_fpu_pnorm_inex
0: lis %r3,0x3FFA       # 1.666666716337204 / 1.25 = 1.3333333730697632 (exact)
   ori %r3,%r3,0xAAAA
   stw %r3,0(%r4)
   lis %r3,0xB800
   stw %r3,4(%r4)
   lfd %f3,0(%r4)
   lis %r3,0x3FA0
   stw %r3,8(%r4)
   lfs %f4,8(%r4)
   fdivs %f3,%f3,%f4
   bl record
   lis %r3,0x3FAA
   ori %r3,%r3,0xAAAB
   stw %r3,12(%r4)
   lfs %f4,12(%r4)
   bl check_fpu_pnorm
0: lfd %f4,0(%r4)       # 1.666666716337204 / 1.3333333730697632 = 1.25 (exact)
   lfs %f3,12(%r4)
   fdivs %f3,%f4,%f3
   bl record
   lfs %f4,8(%r4)
   bl check_fpu_pnorm
   # Unlike the other single-precision instructions, fdivs happily accepts
   # out-of-range inputs and even produces out-of-range results.  It seems
   # that the Cell silently rewrites fdivs to fdiv if an input is out of
   # single-precision range.
0: lfd %f4,336(%r31)    # 2^128 / 2.0
   fdivs %f3,%f4,%f2
   bl record
   lfd %f4,328(%r31)
   bl check_fpu_pnorm
0: lfd %f4,336(%r31)    # 2^128 / 0.5
   lfd %f13,64(%r31)
   fdivs %f3,%f4,%f13
   bl record
   lis %r3,0x4800
   stw %r3,0(%r4)
   stw %r0,4(%r4)
   lfd %f4,0(%r4)
   bl check_fpu_pnorm
0: lfd %f13,0(%r4)      # 2^129 / 1.5
   lfd %f4,296(%r31)
   fdivs %f3,%f13,%f4
   bl record
   lis %r3,0x47F5
   ori %r3,%r3,0x5555
   stw %r3,0(%r4)
   lis %r3,0x5555
   ori %r3,%r3,0x5555
   stw %r3,4(%r4)
   lfd %f4,0(%r4)
   bl check_fpu_pnorm_inex

#todo: uncomment
.if 0
   # fdivs.
0: fdivs. %f3,%f1,%f11  # normal / SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # This is a convenient place to check FPRF values for double-precision
   # denormals since we don't generate them anywhere else.

0: lfd %f13,240(%r31)
   fdiv %f3,%f13,%f2
   bl record
   lfd %f4,248(%r31)
   bl check_fpu_pdenorm
0: fneg %f3,%f2
   fdiv %f3,%f13,%f3
   bl record
   fneg %f4,%f4
   bl check_fpu_ndenorm

   ########################################################################
   # 4.6.5.2 Floating-Point Multiply-Add Instructions
   ########################################################################

   # fmadd
0: fmadd %f3,%f2,%f28,%f1   # normal * normal + normal
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm
0: fmadd %f3,%f0,%f1,%f2    # 0 * normal + normal
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
0: fneg %f4,%f0             # -0 * normal + 0
   fmadd %f3,%f4,%f1,%f0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fneg %f4,%f1             # 0 * -normal + 0
   fmadd %f3,%f0,%f4,%f0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fneg %f4,%f0             # 0 * normal + -0
   fmadd %f3,%f0,%f1,%f4
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: lfd %f3,240(%r31)        # minimum_normal * minimum_normal + -minimum_normal
   fneg %f4,%f3
   fmadd %f3,%f3,%f3,%f4
   bl record
   lfd %f4,240(%r31)
   fneg %f4,%f4
   bl add_fpscr_ux          # Result is tiny and inexact.
   bl check_fpu_nnorm_inex
0: fmadd %f3,%f9,%f2,%f1    # +infinity * normal + normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fmadd %f3,%f9,%f2,%f9    # +infinity * normal + +infinity
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9            # +infinity * -normal + -infinity
   fneg %f2,%f2
   fmadd %f3,%f9,%f2,%f13
   bl record
   fneg %f2,%f2
   fneg %f4,%f9
   bl check_fpu_ninf
0: fneg %f13,%f9            # -infinity * normal + +infinity
   fmadd %f3,%f13,%f2,%f9
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: lfd %f13,320(%r31)       # huge * -huge + +infinity
   fneg %f4,%f13
   fmadd %f3,%f13,%f4,%f9
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fmadd %f3,%f9,%f0,%f1    # +infinity * 0 + normal
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f4,%f9             # +infinity * 0 + -infinity
   fmadd %f3,%f9,%f0,%f4
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f13,%f9            # 0 * -infinity + SNaN
   fmadd %f3,%f0,%f13,%f11
   bl record
   fmr %f4,%f12
   bl add_fpscr_vximz
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fmadd %f3,%f10,%f1,%f2   # QNaN * normal + normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fmadd %f3,%f1,%f11,%f2   # normal * SNaN + normal
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fmadd %f3,%f1,%f2,%f11   # normal * normal + SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fneg %f4,%f9             # +infinity * QNaN + -infinity
   fmadd %f3,%f9,%f10,%f4
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: mtfsf 255,%f0            # SNaN * normal + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmadd %f3,%f11,%f1,%f2
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # 0 * +infinity + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmadd %f3,%f0,%f9,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vximz
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # +infinity * normal + -infinity (exception enabled)
   mtfsb1 24
   fneg %f13,%f9
   fmr %f3,%f24
   fmadd %f3,%f9,%f2,%f13
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24
   # Check that the product is not rounded.
0: mtfsfi 7,1               # 1.333... * 1.5 + 0 (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   fmadd %f3,%f3,%f13,%f0   # Should truncate to (2.0 - 1ulp).
   bl record
   lfd %f4,312(%r31)
   fadd %f3,%f3,%r4         # Should not change the result.
   lfd %f4,304(%r31)
   bl check_fpu_pnorm_inex
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.333... * 1.5 + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fmadd %f3,%f3,%f13,%f4   # Should be exactly 2.0.
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.5 * 1.333... + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fmadd %f3,%f13,%f3,%f4   # Should be exactly 2.0 even for reversed operands.
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0

   # fmadd (FPSCR[FX] handling)
0: fmadd %f4,%f1,%f11,%f2
   mtfsb0 0
   fmadd %f4,%f1,%f11,%f2
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fmadd (exception persistence)
0: fmadd %f4,%f1,%f11,%f2
   fmadd %f4,%f2,%f28,%f1
   bl record
   fmr %f3,%f4
   fmr %f4,%f30
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fmadd.
0: fmadd. %f3,%f1,%f11,%f2  # normal * SNaN + normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0            # normal * SNaN + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fmadd. %f3,%f1,%f3,%f2
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fmadds
0: fmadds %f3,%f2,%f29,%f1  # normal * normal + normal
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm_inex
0: fneg %f13,%f1            # normal * normal + -normal
   lfd %f4,120(%r31)
   fmadds %f3,%f1,%f4,%f13
   bl record
   lfd %f4,200(%r31)        # The multiply result should not be rounded.
   bl check_fpu_pnorm
0: lfs %f3,12(%r30)         # minimum_normal * minimum_normal + -minimum_normal
   fneg %f4,%f3
   fmadds %f3,%f3,%f3,%f4
   bl record
   lfs %f4,12(%r30)
   fneg %f4,%f4
   bl add_fpscr_ux
   bl check_fpu_nnorm_inex
0: mtfsfi 7,1               # 1.333... * 1.5 + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fmadds %f3,%f3,%f13,%f4  # Should be exactly 2.0 even for single precision.
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.5 * 1.333... + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fmadds %f3,%f13,%f3,%f4
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: fneg %f13,%f7            # HUGE_VALF * 2 + -HUGE_VALF
   fmadds %f3,%f7,%f2,%f13
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: fneg %f13,%f7            # 2 * HUGE_VALF + -HUGE_VALF
   fmadds %f3,%f2,%f7,%f13
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: lfd %f13,336(%r31)       # 2^128 * 0.5 + 0
   lfd %f4,64(%r31)
   fmadds %f3,%f13,%f4,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f13,336(%r31)       # 0.5 * 2^128 + 0
   lfd %f4,64(%r31)
   fmadds %f3,%f4,%f13,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)        # 1 * -HUGE_VALF + 2^128
   fneg %f13,%f7
   fmadds %f3,%f1,%f13,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan

#todo: uncomment
   # fmadds.
.if 0
0: fmadds. %f3,%f1,%f11,%f2 # normal * SNaN + normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fmsub
0: fmsub %f3,%f1,%f30,%f1   # normal * normal - normal
   bl record
   fmr %f4,%f24
   bl check_fpu_pnorm
0: fmsub %f3,%f0,%f1,%f2    # 0 * normal - normal
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
0: fneg %f4,%f0             # -0 * normal - 0
   fmsub %f3,%f4,%f1,%f0
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f1             # 0 * -normal - 0
   fmsub %f3,%f0,%f4,%f0
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f0             # 0 * normal - -0
   fmsub %f3,%f0,%f1,%f4
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: lfd %f3,240(%r31)        # minimum_normal * minimum_normal - minimum_normal
   fmsub %f3,%f3,%f3,%f3
   bl record
   lfd %f4,240(%r31)
   fneg %f4,%f4
   bl add_fpscr_ux
   bl check_fpu_nnorm_inex
0: fmsub %f3,%f9,%f2,%f1    # +infinity * normal - normal
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9            # +infinity * normal - -infinity
   fmsub %f3,%f9,%f2,%f13
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f2,%f2             # +infinity * -normal - +infinity
   fmsub %f3,%f9,%f2,%f9
   bl record
   fneg %f2,%f2
   fneg %f4,%f9
   bl check_fpu_ninf
0: fneg %f13,%f9            # -infinity * normal - -infinity
   fmsub %f3,%f13,%f2,%f13
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: lfd %f13,320(%r31)       # huge * -huge - -infinity
   fneg %f4,%f13
   fneg %f3,%f9
   fmsub %f3,%f13,%f4,%f3
   bl record
   fmr %f4,%f9
   bl check_fpu_pinf
0: fmsub %f3,%f9,%f0,%f1    # +infinity * 0 - normal
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fmsub %f3,%f9,%f0,%f9    # +infinity * 0 - infinity
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f13,%f9            # 0 * -infinity - SNaN
   fmsub %f3,%f0,%f13,%f11
   bl record
   fmr %f4,%f12
   bl add_fpscr_vximz
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fmsub %f3,%f10,%f1,%f2   # QNaN * normal - normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fmsub %f3,%f1,%f11,%f2   # normal * SNaN - normal
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fmsub %f3,%f1,%f2,%f11   # normal * normal - SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fmsub %f3,%f9,%f10,%f9   # +infinity * QNaN - infinity
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: mtfsf 255,%f0            # SNaN * normal - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmsub %f3,%f11,%f1,%f2
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # 0 * +infinity - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmsub %f3,%f0,%f9,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vximz
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # +infinity * normal - +infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fmsub %f3,%f9,%f2,%f9
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24

   # fmsub (FPSCR[FX] handling)
0: fmsub %f4,%f1,%f11,%f2
   mtfsb0 0
   fmsub %f4,%f1,%f11,%f2
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fmsub (exception persistence)
0: fmsub %f4,%f1,%f11,%f2
   fmsub %f4,%f1,%f30,%f1
   bl record
   fmr %f3,%f4
   fmr %f4,%f24
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fmsub.
0: fmsub. %f3,%f1,%f11,%f2  # normal * SNaN - normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0            # normal * SNaN - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fmsub. %f3,%f1,%f3,%f2
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fmsubs
0: fneg %f13,%f1            # normal * normal - -normal
   fmsubs %f3,%f2,%f29,%f13
   bl record
   fmr %f4,%f30
   bl check_fpu_pnorm_inex
0: lfd %f4,120(%r31)        # normal * normal - normal
   fmsubs %f3,%f1,%f4,%f1
   bl record
   lfd %f4,200(%r31)
   bl check_fpu_pnorm
0: lfs %f3,12(%r30)         # minimum_normal * minimum_normal - minimum_normal
   fmsubs %f3,%f3,%f3,%f3
   bl record
   lfs %f4,12(%r30)
   fneg %f4,%f4
   bl add_fpscr_ux
   bl check_fpu_nnorm_inex
0: mtfsfi 7,1               # 1.333... * 1.5 - -1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fneg %f4,%f4
   fmsubs %f3,%f3,%f13,%f4
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.5 * 1.333... - -1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fneg %f4,%f4
   fmsubs %f3,%f13,%f3,%f4
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
   mtfsfi 7,0
0: fmsubs %f3,%f7,%f2,%f7   # HUGE_VALF * 2 - HUGE_VALF
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: fmsubs %f3,%f2,%f7,%f7   # 2 * HUGE_VALF - HUGE_VALF
   bl record
   fmr %f4,%f7
   bl check_fpu_pnorm
0: lfd %f13,336(%r31)       # 2^128 * 0.5 - 0
   lfd %f4,64(%r31)
   fmsubs %f3,%f13,%f4,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f13,336(%r31)       # 0.5 * 2^128 - 0
   lfd %f4,64(%r31)
   fmsubs %f3,%f4,%f13,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)        # 1 * HUGE_VALF - 2^128
   fmsubs %f3,%f1,%f7,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fmsubs.
0: fmsubs. %f3,%f1,%f11,%f2 # normal * SNaN - normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fnmadd
0: fnmadd %f3,%f2,%f28,%f1  # normal * normal + normal
   bl record
   fneg %f4,%f30
   bl check_fpu_nnorm
0: fnmadd %f3,%f0,%f1,%f2   # 0 * normal + normal
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
0: fneg %f4,%f0             # -0 * normal + 0
   fnmadd %f3,%f4,%f1,%f0
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f1             # 0 * -normal + 0
   fnmadd %f3,%f0,%f4,%f0
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fneg %f4,%f0             # 0 * normal + -0
   fnmadd %f3,%f0,%f1,%f4
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: lfd %f3,240(%r31)        # minimum_normal * minimum_normal + -minimum_normal
   fneg %f4,%f3
   fnmadd %f3,%f3,%f3,%f4
   bl record
   lfd %f4,240(%r31)
   bl add_fpscr_ux
   bl check_fpu_pnorm_inex
0: fnmadd %f3,%f9,%f2,%f1   # +infinity * normal + normal
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fnmadd %f3,%f9,%f2,%f9   # +infinity * normal + +infinity
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fneg %f13,%f9            # +infinity * -normal + -infinity
   fneg %f2,%f2
   fnmadd %f3,%f9,%f2,%f13
   bl record
   fneg %f2,%f2
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9            # -infinity * normal + +infinity
   fnmadd %f3,%f13,%f2,%f9
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: lfd %f13,320(%r31)       # huge * -huge + +infinity
   fneg %f4,%f13
   fnmadd %f3,%f13,%f4,%f9
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fnmadd %f3,%f9,%f0,%f1   # +infinity * 0 + normal
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f4,%f9             # +infinity * 0 + -infinity
   fnmadd %f3,%f9,%f0,%f4
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f13,%f9            # 0 * -infinity + SNaN
   fnmadd %f3,%f0,%f13,%f11
   bl record
   fmr %f4,%f12
   bl add_fpscr_vximz
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fnmadd %f3,%f10,%f1,%f2  # QNaN * normal + normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fnmadd %f3,%f1,%f11,%f2  # normal * SNaN + normal
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fnmadd %f3,%f1,%f2,%f11  # normal * normal + SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fneg %f4,%f9             # +infinity * QNaN + -infinity
   fnmadd %f3,%f9,%f10,%f4
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: mtfsf 255,%f0            # SNaN * normal + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fnmadd %f3,%f11,%f1,%f2
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # 0 * +infinity + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fnmadd %f3,%f0,%f9,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vximz
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # +infinity * normal + -infinity (exception enabled)
   mtfsb1 24
   fneg %f13,%f9
   fmr %f3,%f24
   fnmadd %f3,%f9,%f2,%f13
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24

   # fnmadd (FPSCR[FX] handling)
0: fnmadd %f4,%f1,%f11,%f2
   mtfsb0 0
   fnmadd %f4,%f1,%f11,%f2
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fnmadd (exception persistence)
0: fnmadd %f4,%f1,%f11,%f2
   fnmadd %f4,%f2,%f28,%f1
   bl record
   fmr %f3,%f4
   fneg %f4,%f30
   bl add_fpscr_vxsnan
   bl check_fpu_nnorm

#todo: uncomment
.if 0
   # fnmadd.
0: fnmadd. %f3,%f1,%f11,%f2  # normal * SNaN + normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0            # normal * SNaN + normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fnmadd. %f3,%f1,%f3,%f2
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fnmadds
0: fnmadds %f3,%f2,%f29,%f1 # normal * normal + normal
   bl record
   fneg %f4,%f30
   bl check_fpu_nnorm_inex
0: fneg %f13,%f1            # normal * normal + -normal
   lfd %f4,120(%r31)
   fnmadds %f3,%f1,%f4,%f13
   bl record
   lfd %f4,200(%r31)
   fneg %f4,%f4
   bl check_fpu_nnorm
0: lfs %f3,12(%r30)         # minimum_normal * minimum_normal + -minimum_normal
   fneg %f4,%f3
   fnmadds %f3,%f3,%f3,%f4
   bl record
   lfs %f4,12(%r30)
   bl add_fpscr_ux
   bl check_fpu_pnorm_inex
0: mtfsfi 7,1               # 1.333... * 1.5 + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fnmadds %f3,%f3,%f13,%f4
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.5 * 1.333... + 1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fnmadds %f3,%f13,%f3,%f4
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
   mtfsfi 7,0
0: fneg %f13,%f7            # HUGE_VALF * 2 + -HUGE_VALF
   fnmadds %f3,%f7,%f2,%f13
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm
0: fneg %f13,%f7            # 2 * HUGE_VALF + -HUGE_VALF
   fnmadds %f3,%f2,%f7,%f13
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm
0: lfd %f13,336(%r31)       # 2^128 * 0.5 + 0
   lfd %f4,64(%r31)
   fnmadds %f3,%f13,%f4,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f13,336(%r31)       # 0.5 * 2^128 + 0
   lfd %f4,64(%r31)
   fnmadds %f3,%f4,%f13,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)        # 1 * -HUGE_VALF + 2^128
   fneg %f13,%f7
   fnmadds %f3,%f1,%f13,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fnmadds.
0: fnmadds. %f3,%f1,%f11,%f2 # normal * SNaN + normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fnmsub
0: fnmsub %f3,%f1,%f30,%f1  # normal * normal - normal
   bl record
   fneg %f4,%f24
   bl check_fpu_nnorm
0: fnmsub %f3,%f0,%f1,%f2   # 0 * normal - normal
   bl record
   fmr %f4,%f2
   bl check_fpu_pnorm
0: fneg %f4,%f0             # -0 * normal - 0
   fnmsub %f3,%f4,%f1,%f0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fneg %f4,%f1             # 0 * -normal - 0
   fnmsub %f3,%f0,%f4,%f0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fneg %f4,%f0             # 0 * normal - -0
   fnmsub %f3,%f0,%f1,%f4
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: lfd %f3,240(%r31)        # minimum_normal * minimum_normal - minimum_normal
   fnmsub %f3,%f3,%f3,%f3
   bl record
   lfd %f4,240(%r31)
   bl add_fpscr_ux
   bl check_fpu_pnorm_inex
0: fnmsub %f3,%f9,%f2,%f1   # +infinity * normal - normal
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fneg %f13,%f9            # +infinity * normal - -infinity
   fnmsub %f3,%f9,%f2,%f13
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fneg %f2,%f2             # +infinity * -normal - +infinity
   fnmsub %f3,%f9,%f2,%f9
   bl record
   fneg %f2,%f2
   fmr %f4,%f9
   bl check_fpu_pinf
0: fneg %f13,%f9            # -infinity * normal - -infinity
   fnmsub %f3,%f13,%f2,%f13
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxisi
   bl check_fpu_nan
0: lfd %f13,320(%r31)       # huge * -huge - -infinity
   fneg %f4,%f13
   fneg %f3,%f9
   fnmsub %f3,%f13,%f4,%f3
   bl record
   fneg %f4,%f9
   bl check_fpu_ninf
0: fnmsub %f3,%f9,%f0,%f1   # +infinity * 0 - normal
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fnmsub %f3,%f9,%f0,%f9   # +infinity * 0 - infinity
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vximz
   bl check_fpu_nan
0: fneg %f13,%f9            # 0 * -infinity - SNaN
   fnmsub %f3,%f0,%f13,%f11
   bl record
   fmr %f4,%f12
   bl add_fpscr_vximz
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fnmsub %f3,%f10,%f1,%f2  # QNaN * normal - normal
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fnmsub %f3,%f1,%f11,%f2  # normal * SNaN - normal
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fnmsub %f3,%f1,%f2,%f11  # normal * normal - SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: fnmsub %f3,%f9,%f10,%f9  # +infinity * QNaN - infinity
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: mtfsf 255,%f0            # SNaN * normal - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fnmsub %f3,%f11,%f1,%f2
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # 0 * +infinity - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fnmsub %f3,%f0,%f9,%f1
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vximz
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0            # +infinity * normal - +infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fnmsub %f3,%f9,%f2,%f9
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxisi
   bl check_fpu_noresult
   mtfsb0 24

   # fnmsub (FPSCR[FX] handling)
0: fnmsub %f4,%f1,%f11,%f2
   mtfsb0 0
   fnmsub %f4,%f1,%f11,%f2
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fnmsub (exception persistence)
0: fnmsub %f4,%f1,%f11,%f2
   fnmsub %f4,%f1,%f30,%f1
   bl record
   fmr %f3,%f4
   fneg %f4,%f24
   bl add_fpscr_vxsnan
   bl check_fpu_nnorm

#todo: uncomment
.if 0
   # fnmsub.
0: fnmsub. %f3,%f1,%f11,%f2  # normal * SNaN - normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0            # normal * SNaN - normal (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fnmsub. %f3,%f1,%f3,%f2
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fnmsubs
0: fneg %f13,%f1            # normal * normal - -normal
   fnmsubs %f3,%f2,%f29,%f13
   bl record
   fneg %f4,%f30
   bl check_fpu_nnorm_inex
0: lfd %f4,120(%r31)        # normal * normal - normal
   fnmsubs %f3,%f1,%f4,%f1
   bl record
   lfd %f4,200(%r31)
   fneg %f4,%f4
   bl check_fpu_nnorm
0: lfs %f3,12(%r30)         # minimum_normal * minimum_normal - minimum_normal
   fnmsubs %f3,%f3,%f3,%f3
   bl record
   lfs %f4,12(%r30)
   bl add_fpscr_ux
   bl check_fpu_pnorm_inex
0: mtfsfi 7,1               # 1.333... * 1.5 - -1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fneg %f4,%f4
   fnmsubs %f3,%f3,%f13,%f4
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
   mtfsfi 7,0
0: mtfsfi 7,1               # 1.5 * 1.333... - -1ulp (round toward zero)
   lfd %f3,288(%r31)
   lfd %f13,296(%r31)
   lfd %f4,312(%r31)
   fneg %f4,%f4
   fnmsubs %f3,%f3,%f13,%f4
   bl record
   fneg %f4,%f2
   bl check_fpu_nnorm
   mtfsfi 7,0
0: fnmsubs %f3,%f7,%f2,%f7  # HUGE_VALF * 2 - HUGE_VALF
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm
0: fnmsubs %f3,%f2,%f7,%f7  # 2 * HUGE_VALF - HUGE_VALF
   bl record
   fneg %f4,%f7
   bl check_fpu_nnorm
0: lfd %f13,336(%r31)       # 2^128 * 0.5 - 0
   lfd %f4,64(%r31)
   fnmsubs %f3,%f13,%f4,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f13,336(%r31)       # 0.5 * 2^128 - 0
   lfd %f4,64(%r31)
   fnmsubs %f3,%f4,%f13,%f0
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan
0: lfd %f4,336(%r31)        # 1 * HUGE_VALF - 2^128
   fnmsubs %f3,%f1,%f7,%f4
   bl record
   lfd %f4,168(%r31)
   bl check_fpu_nan

#todo: uncomment
.if 0
   # fnmsubs.
0: fnmsubs. %f3,%f1,%f11,%f2 # normal * SNaN - normal
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   ########################################################################
   # 4.6.6 Floating-Point Rounding and Conversion Instructions - fcti*
   ########################################################################

   # Swap out some constants.
0: lfd %f24,120(%r31)  # 4194304.75
   fneg %f25,%f24      # -4194304.75
   fmr %f26,%f9        # +infinity
   fneg %f27,%f9       # -infinity
   lfd %f28,208(%r31)  # (double) 2^31
   lfd %f29,216(%r31)  # (double) -(2^31+1)
   lfd %f30,224(%r31)  # (double) 2^63
   lfd %f31,232(%r31)  # (double) -(2^63+2^11)
   lfd %f7,64(%r31)    # 0.5
   fadd %f8,%f7,%f1    # 1.5
   lis %r24,0x40       # 4194304
   addi %r25,%r24,1    # 4194305
   neg %r26,%r24       # -4194304
   neg %r27,%r25       # -4194305
   lis %r29,-0x8000    # -2^31
   not %r28,%r29       # 2^31-1
   sldi %r11,%r29,32   # -2^63
   not %r10,%r11       # 2^63-1

   # fctid (RN = round to nearest)
0: fctid %f3,%f0
   bl record
   li %r7,0
   bl check_fctid
0: fctid %f3,%f1
   bl record
   li %r7,1
   bl check_fctid
0: fneg %f3,%f1
   fctid %f3,%f3
   bl record
   li %r7,-1
   bl check_fctid
0: fctid %f3,%f7
   bl record
   li %r7,0
   bl check_fctid_inex
0: fctid %f3,%f8
   bl record
   li %r7,2
   bl check_fctid_inex
0: fctid %f3,%f24
   bl record
   mr %r7,%r25
   bl check_fctid_inex
0: fctid %f3,%f25
   bl record
   mr %r7,%r27
   bl check_fctid_inex
0: fctid %f3,%f26
   bl record
   mr %r7,%r10
   bl add_fpscr_vxcvi
   bl check_fctid
0: fctid %f3,%f27
   bl record
   mr %r7,%r11
   bl add_fpscr_vxcvi
   bl check_fctid
0: fctid %f3,%f30
   bl record
   mr %r7,%r10
   bl add_fpscr_vxcvi
   bl check_fctid
0: fneg %f4,%f30
   fctid %f3,%f4
   bl record
   mr %r7,%r11
   bl check_fctid
0: fctid %f3,%f31
   bl record
   mr %r7,%r11
   bl add_fpscr_vxcvi
   bl check_fctid
0: fctid %f3,%f10
   bl record
   mr %r7,%r11
   bl add_fpscr_vxcvi
   bl check_fctid
0: fctid %f3,%f11
   bl record
   mr %r7,%r11
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctid

   # fctid (RN = round toward zero)
0: mtfsfi 7,1
   fctid %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctid_inex
0: fctid %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctid_inex

   # fctid (RN = round toward +infinity)
0: mtfsfi 7,2
   fctid %f3,%f24
   bl record
   mr %r7,%r25
   bl check_fctid_inex
0: fctid %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctid_inex

   # fctid (RN = round toward -infinity)
0: mtfsfi 7,3
   fctid %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctid_inex
0: fctid %f3,%f25
   bl record
   mr %r7,%r27
   bl check_fctid_inex

   # fctid (exceptions enabled)
0: mtfsfi 7,0
   mtfsb1 24
   fmr %f3,%f1
   fmr %f4,%f1
   fctid %f4,%f26
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctid %f4,%f30
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctid %f4,%f10
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctid %f4,%f11
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
   mtfsb0 24

   # fctid (FPSCR[FX] handling)
0: fmr %f3,%f11
   fctid %f4,%f3
   mtfsb0 0
   fctid %f4,%f3
   bl record
   fmr %f3,%f4
   mr %r7,%r11
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl remove_fpscr_fx
   bl check_fctid

   # fctid (exception persistence)
0: fmr %f3,%f11
   fctid %f4,%f3
   fmr %f4,%f1
   fctid %f4,%f4
   bl record
   fmr %f3,%f4
   li %r7,1
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctid

#todo: uncomment
.if 0
   # fctid.
0: fctid. %f3,%f11  # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: mr %r7,%r11
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctid
0: mtfsf 255,%f0    # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fctid. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
   mtfsb0 24
.endif

   # fctidz
0: fctidz %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctid_inex
0: fctidz %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctid_inex

#todo: uncomment
.if 0
   # fctidz.
0: fctidz. %f3,%f11
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: mr %r7,%r11
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctid
.endif

   # fctiw (RN = round to nearest)
0: fctiw %f3,%f0
   bl record
   li %r7,0
   bl check_fctiw
0: fctiw %f3,%f1
   bl record
   li %r7,1
   bl check_fctiw
0: fneg %f3,%f1
   fctiw %f3,%f3
   bl record
   li %r7,-1
   bl check_fctiw
0: fctiw %f3,%f7
   bl record
   li %r7,0
   bl check_fctiw_inex
0: fctiw %f3,%f8
   bl record
   li %r7,2
   bl check_fctiw_inex
0: fctiw %f3,%f24
   bl record
   mr %r7,%r25
   bl check_fctiw_inex
0: fctiw %f3,%f25
   bl record
   mr %r7,%r27
   bl check_fctiw_inex
0: fctiw %f3,%f26
   bl record
   mr %r7,%r28
   bl add_fpscr_vxcvi
   bl check_fctiw
0: fctiw %f3,%f27
   bl record
   mr %r7,%r29
   bl add_fpscr_vxcvi
   bl check_fctiw
0: fctiw %f3,%f28
   bl record
   mr %r7,%r28
   bl add_fpscr_vxcvi
   bl check_fctiw
0: fneg %f4,%f28
   fctiw %f3,%f4
   bl record
   mr %r7,%r29
   bl check_fctiw
0: fctiw %f3,%f29
   bl record
   mr %r7,%r29
   bl add_fpscr_vxcvi
   bl check_fctiw
0: fctiw %f3,%f10
   bl record
   mr %r7,%r29
   bl add_fpscr_vxcvi
   bl check_fctiw
0: fctiw %f3,%f11
   bl record
   mr %r7,%r29
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctiw

   # fctiw (RN = round toward zero)
0: mtfsfi 7,1
   fctiw %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctiw_inex
0: fctiw %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctiw_inex

   # fctiw (RN = round toward +infinity)
0: mtfsfi 7,2
   fctiw %f3,%f24
   bl record
   mr %r7,%r25
   bl check_fctiw_inex
0: fctiw %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctiw_inex

   # fctiw (RN = round toward -infinity)
0: mtfsfi 7,3
   fctiw %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctiw_inex
0: fctiw %f3,%f25
   bl record
   mr %r7,%r27
   bl check_fctiw_inex

   # fctiw (exceptions enabled)
0: mtfsfi 7,0
   mtfsb1 24
   fmr %f3,%f1
   fmr %f4,%f1
   fctiw %f4,%f26
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctiw %f4,%f28
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctiw %f4,%f10
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
0: fctiw %f4,%f11
   bl record
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
   mtfsb0 24

   # fctiw (FPSCR[FX] handling)
0: fmr %f3,%f11
   fctiw %f4,%f3
   mtfsb0 0
   fctiw %f4,%f3
   bl record
   fmr %f3,%f4
   mr %r7,%r29
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl remove_fpscr_fx
   bl check_fctiw

   # fctiw (exception persistence)
0: fmr %f3,%f11
   fctiw %f4,%f3
   fmr %f4,%f1
   fctiw %f4,%f4
   bl record
   fmr %f3,%f4
   li %r7,1
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctiw

#todo: uncomment
.if 0
   # fctiw.
0: fctiw. %f3,%f11  # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: mr %r7,%r29
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctiw
0: mtfsf 255,%f0    # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fctiw. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fpu_noresult_nofprf
   mtfsb0 24
.endif

   # fctiwz
0: fctiwz %f3,%f24
   bl record
   mr %r7,%r24
   bl check_fctiw_inex
0: fctiwz %f3,%f25
   bl record
   mr %r7,%r26
   bl check_fctiw_inex

#todo: uncomment
.if 0
   # fctiwz.
0: fctiwz. %f3,%f11
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: mr %r7,%r29
   bl add_fpscr_vxsnan
   bl add_fpscr_vxcvi
   bl check_fctiw
.endif

   ########################################################################
   # 4.6.6 Floating-Point Rounding and Conversion Instructions - fcfid
   ########################################################################

   # fcfid
0: fcfid %f3,%f0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: li %r3,1
   std %r3,0(%r4)
   lfd %f3,0(%r4)
   fcfid %f3,%f3
   bl record
   fmr %f4,%f1
   bl check_fpu_pnorm
0: li %r3,-1
   std %r3,0(%r4)
   lfd %f4,0(%r4)
   fcfid %f3,%f4
   bl record
   fneg %f4,%f1
   bl check_fpu_nnorm
0: srdi %r3,%r3,1
   std %r3,0(%r4)
   lfd %f13,0(%r4)
   fcfid %f3,%f13
   bl record
   lis %r7,0x43E0
   sldi %r7,%r7,32
   std %r7,0(%r4)
   lfd %f4,0(%r4)
   bl check_fpu_pnorm_inex
0: not %r3,%r3
   std %r3,0(%r4)
   lfd %f31,0(%r4)
   fcfid %f3,%f31
   bl record
   lis %r7,0xC3E0
   sldi %r7,%r7,32
   std %r7,0(%r4)
   lfd %f4,0(%r4)
   bl check_fpu_nnorm

#todo: uncomment
   # fcfid.
   # This instruction can't generate exceptions, so use another insn to
   # prime FPSCR so we can usefully check CR1.
.if 0
0: fdiv %f3,%f0,%f0
   fcfid. %f3,%f0
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f0
   bl add_fpscr_vxzdz
   bl check_fpu_pzero
.endif

   ########################################################################
   # 5.1.1 (Optional) Move To/From System Register Instructions
   ########################################################################

   # mfocrf
0: li %r3,0
   cmpdi cr7,%r3,0
   mfocrf %r3,1
   bl record
   andi. %r3,%r3,15
   cmpdi %r3,2
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # mtocrf
0: lis %r3,0x4000
   mtocrf 128,%r3
   bl record
   bgt 0f
   addi %r6,%r6,32
0: lis %r3,0x0200
   mtocrf 64,%r3
   bl record
   bgt 1f
   addi %r6,%r6,32
1: beq cr1,0f
   addi %r6,%r6,32

0: li 0,%r0
   mtcr %r0

   ########################################################################
   # 5.2.1 (Optional) Floating-Point Arithmetic Instructions
   ########################################################################

   # Load constants.
0: lfd %f24,80(%r31)    # 4194304.0
   lfd %f25,176(%r31)   # 2048.0
   lfd %f28,64(%r31)    # 0.5
   lfd %f29,56(%r31)    # 0.25

   # fsqrt
0: fsqrt %f3,%f24       # +normal
   bl record
   fmr %f4,%f25
   bl check_fpu_pnorm
0: fsqrt %f3,%f0        # +0
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fsqrt %f3,%f26       # +infinity
   bl record
   fmr %f4,%f26
   bl check_fpu_pinf
0: fneg %f3,%f24        # -normal
   fsqrt %f3,%f3
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxsqrt
   bl check_fpu_nan
0: fneg %f4,%f0         # -0
   fsqrt %f3,%f4
   bl record
   bl check_fpu_nzero
0: fsqrt %f3,%f10       # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fsqrt %f3,%f11       # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f5,%f11
   fmr %f3,%f24
   fsqrt %f3,%f5
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # -infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   fsqrt %f3,%f27
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsqrt
   bl check_fpu_noresult
   mtfsb0 24

   # fsqrt (FPSCR[FX] handling)
0: fsqrt %f4,%f11
   mtfsb0 0
   fsqrt %f4,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fsqrt (exception persistence)
0: fsqrt %f4,%f11
   fsqrt %f4,%f24
   bl record
   fmr %f3,%f4
   fmr %f4,%f25
   bl add_fpscr_vxsnan
   bl check_fpu_pnorm

#todo: uncomment
.if 0
   # fsqrt.
0: fsqrt. %f3,%f11      # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fsqrt. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # fsqrts
   # The square root of any base-2 rational number will always have fewer
   # significant digits than the original number, so we use an irrational
   # number: sqrt(2) = 0b1.011 0101 0000 0100 1111 0011 0... (rounding down
   # to 0x3FB504F3) to test single-precision rounding.
0: fsqrts %f3,%f2       # normal
   bl record
   lfs %f4,8(%r30)
   bl check_fpu_pnorm_inex

#todo: uncomment
.if 0
   # fsqrts.
0: fsqrts. %f3,%f11     # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
.endif

   # fres
0: fres %f3,%f2         # +normal
   bl record
   # The instruction description says that the result is "correct within
   # one part in 256", so check that it falls within the proper bounds.
   # FIXME: Figure out the actual algorithm used by the hardware and test
   # for its precise results.
   lfd %f4,256(%r31)
   lfd %f5,264(%r31)
   bl check_fpu_estimate
0: fres %f3,%f26        # +infinity
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: fres %f3,%f27        # -infinity
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fres %f3,%f0         # +0
   bl record
   fmr %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_pinf
0: fneg %f3,%f0         # -0
   fres %f3,%f3
   bl record
   fneg %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_ninf
0: lfd %f13,336(%r31)   # 2^128 (out of range)
   fres %f3,%f3
   bl record
   fneg %f4,%f0
   bl check_fpu_nzero
0: fres %f3,%f10        # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: fres %f3,%f11        # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f5,%f11
   fmr %f3,%f24
   fres %f3,%f5
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsb1 27            # 0 (exception enabled)
   fmr %f3,%f24
   fmr %f4,%f0
   fres %f3,%f4
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_zx
   bl check_fpu_noresult
   mtfsb0 27

   # fres (FPSCR[FX] handling)
0: fres %f4,%f11
   mtfsb0 0
   fres %f4,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # fres (exception persistence)
0: fres %f4,%f11
   fres %f4,%f2
   bl record
   fmr %f3,%f4
   lfd %f4,256(%r31)
   lfd %f5,264(%r31)
   bl add_fpscr_vxsnan
   bl check_fpu_estimate

#todo: uncomment
.if 0
   # fres.
0: fres. %f3,%f11       # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   fres. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   # frsqrte
   # FIXME: Figure out the actual algorithm used by the hardware and test
   # for its precise results.
0: frsqrte %f3,%f29     # +normal
   bl record
   lfd %f4,272(%r31)
   lfd %f5,280(%r31)
   bl check_fpu_estimate
0: frsqrte %f3,%f26     # +infinity
   bl record
   fmr %f4,%f0
   bl check_fpu_pzero
0: frsqrte %f3,%f0      # +0
   bl record
   fmr %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_pinf
0: fneg %f3,%f0
   frsqrte %f3,%f3      # -0
   bl record
   fneg %f4,%f9
   bl add_fpscr_zx
   bl check_fpu_ninf
0: fneg %f6,%f29        # -normal
   frsqrte %f3,%f6
   bl record
   lfd %f4,168(%r31)
   bl add_fpscr_vxsqrt
   bl check_fpu_nan
0: frsqrte %f3,%f10     # QNaN
   bl record
   fmr %f4,%f10
   bl check_fpu_nan
0: frsqrte %f3,%f11     # SNaN
   bl record
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f5,%f11
   fmr %f3,%f24
   frsqrte %f3,%f5
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsf 255,%f0        # -infinity (exception enabled)
   mtfsb1 24
   fmr %f3,%f24
   frsqrte %f3,%f27
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_vxsqrt
   bl check_fpu_noresult
   mtfsb0 24
0: mtfsb1 27            # -0 (exception enabled)
   fmr %f3,%f24
   fneg %f4,%f0
   frsqrte %f3,%f4
   bl record
   fmr %f4,%f24
   bl add_fpscr_fex
   bl add_fpscr_zx
   bl check_fpu_noresult
   mtfsb0 27

   # frsqrte (FPSCR[FX] handling)
0: frsqrte %f4,%f11
   mtfsb0 0
   frsqrte %f4,%f11
   bl record
   fmr %f3,%f4
   fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl remove_fpscr_fx
   bl check_fpu_nan

   # frsqrte (exception persistence)
0: frsqrte %f4,%f11
   frsqrte %f4,%f29
   bl record
   fmr %f3,%f4
   lfd %f4,272(%r31)
   lfd %f5,280(%r31)
   bl add_fpscr_vxsnan
   bl check_fpu_estimate

#todo: uncomment
.if 0
   # frsqrte.
0: frsqrte. %f3,%f11    # SNaN
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f12
   bl add_fpscr_vxsnan
   bl check_fpu_nan
0: mtfsf 255,%f0        # SNaN (exception enabled)
   mtfsb1 24
   fmr %f3,%f11
   frsqrte. %f3,%f3
   bl record
   mfcr %r3
   lis %r7,0x0E00
   cmpw %r3,%r7
   beq 1f
   std %r3,16(%r6)
   li %r3,-1
   std %r3,8(%r6)
   addi %r6,%r6,32
   mtcr %r0
   mtfsf 255,%f0
   b 0f
1: fmr %f4,%f11
   bl add_fpscr_fex
   bl add_fpscr_vxsnan
   bl check_fpu_noresult
   mtfsb0 24
.endif

   ########################################################################
   # 5.2.2 (Optional) Floating-Point Select Instruction
   ########################################################################

   # fsel
0: fsel %f3,%f2,%f1,%f0     # +normal
   bl record
   fcmpu cr0,%f3,%f1
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32
0: fsel %f3,%f0,%f2,%f0     # +0
   bl record
   fcmpu cr0,%f3,%f2
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32
0: fneg %f3,%f0             # -0
   fsel %f3,%f3,%f1,%f0
   bl record
   fcmpu cr0,%f3,%f1
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32
0: fneg %f4,%f1             # -normal
   fsel %f3,%f4,%f0,%f2
   bl record
   fcmpu cr0,%f3,%f2
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32
0: fsel %f3,%f10,%f0,%f1    # QNaN
   bl record
   fcmpu cr0,%f3,%f1
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32
0: mtfsf 255,%f0            # SNaN
   fsel %f3,%f11,%f0,%f2
   bl record
   mffs %f4                 # The SNaN should not generate an exception.
   stfd %f4,0(%r4)
   lwz %r3,4(%r4)
   fadd %f4,%f0,%f0         # Make sure the SNaN doesn't leak an exception
   mffs %f4                 # to the next FPU operation either.
   stfd %f4,0(%r4)
   lwz %r7,4(%r4)
   cmpwi %r3,0
   bne 1f
   cmpwi %r7,0x2000
   beq 2f
1: stfd %f3,8(%r6)
   stw %r3,16(%r6)
   stw %r7,20(%r6)
   addi %r6,%r6,32
   b 0f
2: fcmpu cr0,%f3,%f2
   beq 0f
   stfd %f3,8(%r6)
   addi %r6,%r6,32

#todo: uncomment
.if 0
   # fsel.
0: li %r0,0
   mtcr %r0
   fadd %f3,%f11,%f11       # Record an exception for fsel. to pick up.
   fsel. %f3,%f2,%f1,%f0
   bl record
   mfcr %r3
   lis %r7,0x0A00
   cmpw %r3,%r7
   bne 1f
   fcmpu cr0,%f3,%f1
   beq 0f
1: stfd %f3,8(%r6)
   std %r3,16(%r6)
   addi %r6,%r6,32
.endif

   ########################################################################
   # Book II 3.2.1 Instruction Cache Instruction
   ########################################################################

   # This and many of the following instructions have no visible effect on
   # program state; they are included only to ensure that instruction
   # decoders properly accept the instructions.

   # Load r11 with the address of label 2.
0: bl 1f
2: b 0f
1: mflr %r11
   blr

   # icbi
0: li %r3,0f-2b
   icbi %r11,%r3
0: addi %r11,%r11,0f-2b
   lis %r0,0x8000
   icbi 0,%r11

   ########################################################################
   # Book II 3.2.2 Data Cache Instructions
   ########################################################################

   # dcbt
0: dcbt %r4,%r3
0: dcbt 0,%r4

   # dcbtst
0: dcbtst %r4,%r3
0: dcbtst 0,%r4

   # dcbz
0: li %r7,1
   stw %r7,0(%r4)
   li %r7,0
   dcbz %r4,%r7
   bl record
   lwz %r7,0(%r4)
   cmpdi %r7,0
   beq 0f
   std %r7,8(%r6)
   addi %r6,%r6,32
0: li %r7,1
   stw %r7,0(%r4)
   li %r0,0x4000    # Assume this is at least as large as a cache line.
   dcbz 0,%r4
   bl record
   lwz %r7,0(%r4)
   cmpdi %r7,0
   beq 0f
   std %r7,8(%r6)
   addi %r6,%r6,32

   # dcbst
0: dcbst %r4,%r3
0: dcbst 0,%r4

   # dcbf
0: li %r7,0x3FFC  # Careful not to flush anything we actually need!
   dcbf %r4,%r7
0: add %r7,%r4,%r7
   li %r0,-0x3FFC
   dcbf 0,%r4

   ########################################################################
   # Book II 3.3.1 Instruction Synchronize Instruction
   ########################################################################

   # isync
0: isync

   ########################################################################
   # Book II 3.3.2 Load and Reserve and Store Conditional Instructions
   ########################################################################

0: li %r11,-1
   stw %r11,0(%r4)
   stw %r11,4(%r4)
   stw %r11,8(%r4)
   stw %r11,12(%r4)
   stw %r11,16(%r4)

   # lwarx/stwcx.
0: li %r0,0
   stw %r0,4(%r4)
   li %r7,4
   lwarx %r3,%r4,%r7  # rA != 0
   bl record
   cmpdi %r3,0
   beq 0f
   addi %r6,%r6,32
0: li %r3,1
   stwcx. %r3,%r4,%r7
   bl record
   li %r3,-1
   bne 1f
   lwz %r3,4(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r8,2
   stwcx. %r8,%r4,%r7  # No reservation, so this will fail.
   bl record
   li %r3,-1
   beq 1f
   lwz %r3,4(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

0: stw %r0,4(%r4)
   addi %r7,%r4,4
   li %r0,4
   lwarx %r3,0,%r7  # rA == 0
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,1
   stwcx. %r3,0,%r7
   bl record
   li %r3,-1
   bne 1f
   lwz %r3,4(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r8,2
   stwcx. %r8,0,%r7
   bl record
   li %r3,-1
   beq 1f
   lwz %r3,4(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

   # Check that stwcx. to the wrong address still succeeds.
0: li %r0,0
   stw %r0,4(%r4)
   li %r7,4
   lwarx %r3,%r4,%r7
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,1
   stwcx. %r3,0,%r4
   bl record
   li %r3,-1
   li %r7,-1
   bne 1f
   lwz %r3,0(%r4)
   cmpdi %r3,1
   li %r7,0
   bne 1f
   lwz %r3,4(%r4)   # Also make sure nothing was written to the lwarx address.
   cmpdi %r3,0
   li %r7,4
   beq 0f
1: std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # ldarx/stdcx.
0: li %r0,0
   std %r0,8(%r4)
   li %r7,8
   ldarx %r3,%r4,%r7
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,1
   stdcx. %r3,%r4,%r7
   bl record
   li %r3,-1
   bne 1f
   ld %r3,8(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r8,2
   stdcx. %r8,%r4,%r7
   bl record
   li %r3,-1
   beq 1f
   ld %r3,8(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

0: std %r0,8(%r4)
   addi %r7,%r4,8
   li %r0,8
   ldarx %r3,0,%r7
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,1
   stdcx. %r3,0,%r7
   bl record
   li %r3,-1
   bne 1f
   ld %r3,8(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r8,2
   stdcx. %r8,0,%r7
   bl record
   li %r3,-1
   beq 1f
   ld %r3,8(%r4)
   cmpdi %r3,1
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

0: li %r0,0
   std %r0,8(%r4)
   li %r7,8
   ldarx %r3,%r4,%r7
   bl record
   cmpdi %r3,0
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,1
   stdcx. %r3,0,%r4
   stdcx. %r8,%r4,%r7
   bl record
   li %r3,-1
   beq 1f
   ld %r3,8(%r4)
   cmpdi %r3,0
   beq 0f
1: std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # Book II 3.3.3 Memory Barrier Instructions
   ########################################################################

   # sync
0: sync 0           # sync
0: sync 1           # lwsync
0: sync 2           # ptesync

   # eieio
0: eieio

   ########################################################################
   # Book II 4.1 Time Base Instructions
   ########################################################################

   # mftb
   # Some versions of binutils-as incorrectly encode this as mfspr, so
   # code the instruction directly.
0: .int 0x7C6C42E6  # mftb %r3
   li %r0,MFTB_SPIN_COUNT
   mtctr %r0
1: bdnz 1b
   .int 0x7CEC42E6  # mftb %r7
   bl record
   sub. %r3,%r7,%r3
   bgt 0f
   std %r3,8(%r6)
   std %r7,16(%r6)
   addi %r6,%r6,32

   # mftbu
0: .int 0x7D4C42E6  # mftb %r10
   .int 0x7CED42E6  # mftbu %r7
   bl record
   srdi %r3,%r10,32
   sub %r3,%r7,%r3
   cmpdi %r3,0
   beq 0f
   cmpdi %r3,1      # The low 32 bits might have rolled over.
   beq 0f
   std %r3,8(%r6)
   std %r7,16(%r6)
   std %r10,24(%r6)
   addi %r6,%r6,32

   ########################################################################
   # Vector Processing Instructions: Data stream control
   ########################################################################

   # The Cell processor treats all these instructions as no-ops, so just
   # check that they can be decoded.
0: dss 0
0: dssall
0: li %r3,16
   dst %r4,%r3,0
0: dstt %r4,%r3,0
0: dstst %r4,%r3,0
0: dststt %r4,%r3,0

   ########################################################################
   # Vector Processing Instructions: Load/store vector
   ########################################################################

0: li %r3,256
   li %r0,256
   mtctr %r0
1: stbx %r3,%r4,%r3
   addi %r3,%r3,1
   bdnz 1b

   # lvx/stvx
0: li %r0,0
   li %r3,0x120
   lvx %v0,%r4,%r3
   bl record
   stvx %v0,%r4,%r0
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r7,0x120(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x128(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: li %r0,0x10
   addi %r3,%r4,0x130
   lvx %v0,%r0,%r3
   bl record
   stvx %v0,%r0,%r4
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r7,0x130(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x138(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: li %r0,7         # The low 4 bits of the address should be ignored.
   li %r3,0x14F
   lvx %v1,%r4,%r3
   bl record
   stvx %v1,%r4,%r0
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r7,0x140(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x148(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   # lvxl
   # The "load/store last" instructions don't have any program-visible
   # difference from the ordinary load instructions, so we just run one of
   # each to check that they are decoded correctly.
0: li %r0,0
   li %r3,0x160
   lvxl %v0,%r4,%r3
   bl record
   stvxl %v0,%r4,%r0
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r7,0x160(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x168(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   ########################################################################
   # Vector Processing Instructions: Load/store element
   ########################################################################

   # lvebx
0: li %r0,0
   li %r3,0x123
   lvebx %v0,%r4,%r3
   bl record
   stv %v0,0,%r4
   lbz %r3,3(%r4)
   cmpwi %r3,0x23
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32
0: li %r0,0x10
   addi %r3,%r4,0x111
   lvebx %v0,0,%r3  # Also test the case of RA=0.
   bl record
   stv %v0,0,%r4
   lbz %r3,1(%r4)
   cmpwi %r3,0x11
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32

   # lvehx
0: li %r0,0
   li %r3,0x136
   lvehx %v0,%r4,%r3
   bl record
   stv %v0,0,%r4
   lhz %r3,6(%r4)
   cmpwi %r3,0x3637
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32
0: li %r0,0x10
   addi %r3,%r4,0x149  # The low bit of the address should be ignored.
   lvehx %v0,0,%r3
   bl record
   stv %v0,0,%r4
   lhz %r3,8(%r4)
   cmpwi %r3,0x4849
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32

   # lvewx
0: li %r0,0
   li %r3,0x15C
   lvewx %v0,%r4,%r3
   bl record
   stv %v0,0,%r4
   lwz %r3,12(%r4)
   lwz %r7,0x15C(%r4)
   cmpw %r3,%r7
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32
0: li %r0,0x10
   addi %r3,%r4,0x16F  # The low 2 bits of the address should be ignored.
   lvewx %v0,0,%r3
   bl record
   stv %v0,0,%r4
   lwz %r3,12(%r4)
   lwz %r7,0x16C(%r4)
   cmpw %r3,%r7
   beq 0f
   std %r3,8(%r4)
   addi %r6,%r6,32

   # stvebx
0: li %r0,0
   std %r0,0(%r4)
   std %r0,8(%r4)
   lv %v0,0x120,%r4
   li %r3,3
   stvebx %v0,%r4,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   li %r7,0x23
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpdi %r8,0
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32
0: std %r0,0(%r4)
   std %r0,8(%r4)
   lv %v0,0x110,%r4
   addi %r3,%r4,1
   li %r0,0x10
   stvebx %v0,0,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   lis %r7,0x11
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpdi %r8,0
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32

   # stvehx
0: li %r0,0
   std %r0,0(%r4)
   std %r0,8(%r4)
   li %r3,0x130
   lv %v0,0x130,%r4
   li %r3,6
   stvehx %v0,%r4,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   cmpdi %r3,0x3637
   bne 1f
   cmpdi %r8,0
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32
0: std %r0,0(%r4)
   std %r0,8(%r4)
   lv %v0,0x140,%r4
   addi %r3,%r4,9
   li %r0,0x10
   stvehx %v0,0,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   cmpdi %r3,0
   bne 1f
   lis %r7,0x4849
   sldi %r7,%r7,32
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32

   # stvewx
0: li %r0,0
   std %r0,0(%r4)
   std %r0,8(%r4)
   lv %v0,0x150,%r4
   li %r3,12
   stvewx %v0,%r4,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   cmpdi %r3,0
   bne 1f
   lwz %r7,0x15C(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32
0: std %r0,0(%r4)
   std %r0,8(%r4)
   lv %v0,0x160,%r4
   addi %r3,%r4,15
   li %r0,0x10
   stvewx %v0,0,%r3
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   cmpdi %r3,0
   bne 1f
   lwz %r7,0x16C(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r4)
   std %r8,24(%r4)
   addi %r6,%r6,32

   ########################################################################
   # Vector Processing Instructions: Load ("splat") immediate to all elements
   ########################################################################

   # vspltb
0: lv %v4,0x120,%r4
   vspltb %v3,%v4,11
   bl record
   stv %v3,0,%r4
   lis %r7,0x2B2B
   ori %r7,%r7,0x2B2B
   sldi %r7,%r7,32
   oris %r7,%r7,0x2B2B
   ori %r7,%r7,0x2B2B
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # vsplth
0: lv %v4,0x130,%r4
   vsplth %v3,%v4,4
   bl record
   stv %v3,0,%r4
   lis %r7,0x3839
   ori %r7,%r7,0x3839
   sldi %r7,%r7,32
   oris %r7,%r7,0x3839
   ori %r7,%r7,0x3839
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # vspltw
0: lv %v4,0x140,%r4
   vspltw %v3,%v4,1
   bl record
   stv %v3,0,%r4
   lis %r7,0x4445
   ori %r7,%r7,0x4647
   sldi %r7,%r7,32
   oris %r7,%r7,0x4445
   ori %r7,%r7,0x4647
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # vspltisb
0: vspltisb %v3,-3
   bl record
   stv %v3,0,%r4
   lis %r7,0xFDFD
   ori %r7,%r7,0xFDFD
   sldi %r7,%r7,32
   oris %r7,%r7,0xFDFD
   ori %r7,%r7,0xFDFD
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # vspltish
0: vspltish %v3,-4
   bl record
   stv %v3,0,%r4
   lis %r7,0xFFFC
   ori %r7,%r7,0xFFFC
   sldi %r7,%r7,32
   oris %r7,%r7,0xFFFC
   ori %r7,%r7,0xFFFC
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # vspltisw
0: vspltisw %v3,-5
   bl record
   stv %v3,0,%r4
   li %r7,-4
   sldi %r7,%r7,32
   addi %r7,%r7,-5
   ld %r3,0(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   ########################################################################
   # Vector Processing Instructions: Read/write VSCR
   ########################################################################

   # mfvscr/mtvscr
0: lvi %v0,0x10001
   mtvscr %v0
   vspltisb %v1,-1
   mfvscr %v1
   bl record
   stv %v1,0,%r4
   ld %r3,0(%r4)
   cmpdi %r3,0
   bne 1f
   ld %r3,8(%r4)
   lis %r7,1
   ori %r7,%r7,1
   cmpd %r3,%r7
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32
0: vspltisw %v0,0
   mtvscr %v0
   bl record
   vspltisb %v1,-1
   mfvscr %v1
   stv %v1,0,%r4
   ld %r3,0(%r4)
   cmpdi %r3,0
   bne 1f
   ld %r3,8(%r4)
   cmpdi %r3,0
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   ########################################################################
   # Vector Processing Instructions: vcmpequw. (for check_vector_* routines)
   ########################################################################

   # vcmpequw.
0: li %r0,0
   mtcr %r0
   vspltisw %v3,0
   vspltisw %v4,1
   vcmpequw. %v3,%v3,%v4
   bl record
   mfcr %r8
   cmpwi %r8,0x20
   bne 1f
   stv %v3,0,%r4
   ld %r3,0(%r4)
   li %r7,0
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: std %r8,8(%r6)
   stv %v3,16,%r6
   addi %r6,%r6,32
0: mtcr %r0
   vspltisw %v4,1
   vcmpequw. %v3,%v4,%v4
   bl record
   mfcr %r8
   cmpwi %r8,0x80
   bne 1f
   stv %v3,0,%r4
   ld %r3,0(%r4)
   li %r7,-1
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   cmpd %r3,%r7
   beq 0f
1: std %r8,8(%r6)
   stv %v3,16,%r6
   addi %r6,%r6,32
0: mtcr %r0
   lvi %v5,1
   vcmpequw. %v3,%v5,%v4
   bl record
   mfcr %r8
   cmpwi %r8,0
   bne 1f
   stv %v3,0,%r4
   ld %r3,0(%r4)
   li %r7,0
   cmpd %r3,%r7
   bne 1f
   ld %r3,8(%r4)
   li %r7,-1
   srdi %r7,%r7,32
   cmpd %r3,%r7
   beq 0f
1: std %r8,8(%r6)
   stv %v3,16,%r6
   addi %r6,%r6,32

   # Beyond this point it's safe to use the check_vector_* routines which
   # take the expected value in %r4 (but not check_vector_*_literal).

   ########################################################################
   # Vector Processing Instructions: Permutation instructions
   ########################################################################

0: vspltisw %v0,0
   vspltisw %v1,-1
   lv %v24,0x120,%r4
   lv %v25,0x130,%r4
   lv %v26,0x180,%r4

   # lvsl
0: li %r0,0
   li %r3,0x120
   lvsl %v3,%r4,%r3
   bl record
   lv %r4,0x100,%r4
   bl check_vector_int
0: li %r0,0x10
   addi %r3,%r4,0x139
   lvsl %v3,0,%r3
   bl record
   stv %v3,0,%r4
   lwz %r3,0(%r4)
   lwz %r8,4(%r4)
   lwz %r9,8(%r4)
   lwz %r10,12(%r4)
   lis %r7,0x090A
   ori %r7,%r7,0x0B0C
   cmpd %r3,%r7
   bne 1f
   lis %r7,0x0D0E
   ori %r7,%r7,0x0F10
   cmpd %r8,%r7
   bne 1f
   lis %r7,0x1112
   ori %r7,%r7,0x1314
   cmpd %r9,%r7
   bne 1f
   lis %r7,0x1516
   ori %r7,%r7,0x1718
   cmpd %r10,%r7
   beq 0f
1: stw %r3,16(%r6)
   stw %r8,20(%r6)
   stw %r9,24(%r6)
   stw %r10,28(%r6)
   addi %r6,%r6,32

   # vperm
0: lv %v4,0x120,%r4
   lv %v5,0x130,%r4
   lis %r3,0x0E3C   # Set a few high bits to check that they're ignored.
   ori %r3,%r3,0x4C98
   sldi %r3,%r3,32
   oris %r3,%r3,0x0F08
   ori %r3,%r3,0x1B12
   std %r3,0(%r4)
   lis %r3,0x0B1F
   ori %r3,%r3,0x0211
   sldi %r3,%r3,32
   oris %r3,%r3,0x1501
   ori %r3,%r3,0x050B
   std %r3,8(%r4)
   lv %v6,0,%r4
   vperm %v3,%v4,%v5,%v6
   bl record
   lis %r3,0x2020
   ori %r3,%r3,0x2020
   addis %r7,%r3,-0x0101
   addi %r7,%r7,-0x0101  # 0x1F1F1F1F
   sldi %r8,%r3,32
   or %r8,%r8,%r3
   sldi %r9,%r7,32
   or %r9,%r9,%r7
   ld %r3,0(%r4)
   ld %r7,8(%r4)
   and %r3,%r3,%r9
   and %r7,%r7,%r9
   or %r3,%r3,%r8
   or %r7,%r7,%r8
   stv %v3,16,%r4
   ld %r8,16(%r4)
   ld %r9,24(%r4)
   cmpd %r3,%r8
   bne 1f
   cmpd %r7,%r9
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32

   # Beyond this point it's safe to use the check_vector_*_literal routines.

   # Check that the implementation of vperm works correctly when the
   # destination is the same as one of the sources.
0: lv %v3,0x140,%r4
   lv %v5,0x140,%r4
   lis %r3,0x0F00
   ori %r3,%r3,0x0102
   sldi %r3,%r3,32
   oris %r3,%r3,0x1314
   ori %r3,%r3,0x1516
   std %r3,0(%r4)
   lis %r3,0x191A
   ori %r3,%r3,0x1B1C
   sldi %r3,%r3,32
   oris %r3,%r3,0x0D0E
   ori %r3,%r3,0x0F00
   std %r3,8(%r4)
   lv %v7,0,%r4
   vperm %v3,%v3,%v5,%v7
   bl record
   bl check_vector_int_literal
   .int 0x4F404142,0x43444546,0x494A4B4C,0x4D4E4F40
0: lv %v3,0x140,%r4
   lv %v5,0x140,%r4
   vperm %v3,%v5,%v3,%v7
   bl record
   bl check_vector_int_literal
   .int 0x4F404142,0x43444546,0x494A4B4C,0x4D4E4F40

   # lvsr
0: li %r0,0
   li %r3,0x120
   lvsr %v3,%r4,%r3
   bl record
   lv %r4,0x110,%r4
   bl check_vector_int
0: li %r0,0x10
   addi %r3,%r4,0x139
   lvsr %v3,0,%r3
   bl record
   bl check_vector_int_literal
   .int 0x0708090A,0x0B0C0D0E,0x0F101112,0x13141516

   # vmrghb
0: vmrghb %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20302131,0x22322333,0x24342535,0x26362737
0: vmr %v3,%v24
   vmrghb %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20302131,0x22322333,0x24342535,0x26362737
0: vmr %v3,%v25
   vmrghb %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x20302131,0x22322333,0x24342535,0x26362737

   # vmrghh
0: vmrghh %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20213031,0x22233233,0x24253435,0x26273637
0: vmr %v3,%v24
   vmrghh %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20213031,0x22233233,0x24253435,0x26273637
0: vmr %v3,%v25
   vmrghh %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x20213031,0x22233233,0x24253435,0x26273637

   # vmrghw
0: vmrghw %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20212223,0x30313233,0x24252627,0x34353637
0: vmr %v3,%v24
   vmrghw %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x20212223,0x30313233,0x24252627,0x34353637
0: vmr %v3,%v25
   vmrghw %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x20212223,0x30313233,0x24252627,0x34353637

   # vmrglb
0: vmrglb %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28382939,0x2A3A2B3B,0x2C3C2D3D,0x2E3E2F3F
0: vmr %v3,%v24
   vmrglb %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28382939,0x2A3A2B3B,0x2C3C2D3D,0x2E3E2F3F
0: vmr %v3,%v25
   vmrglb %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x28382939,0x2A3A2B3B,0x2C3C2D3D,0x2E3E2F3F

   # vmrglh
0: vmrglh %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28293839,0x2A2B3A3B,0x2C2D3C3D,0x2E2F3E3F
0: vmr %v3,%v24
   vmrglh %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28293839,0x2A2B3A3B,0x2C2D3C3D,0x2E2F3E3F
0: vmr %v3,%v25
   vmrglh %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x28293839,0x2A2B3A3B,0x2C2D3C3D,0x2E2F3E3F

   # vmrglw
0: vmrglw %v3,%v24,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28292A2B,0x38393A3B,0x2C2D2E2F,0x3C3D3E3F
0: vmr %v3,%v24
   vmrglw %v3,%v3,%v25
   bl record
   bl check_vector_int_literal
   .int 0x28292A2B,0x38393A3B,0x2C2D2E2F,0x3C3D3E3F
0: vmr %v3,%v25
   vmrglw %v3,%v24,%v3
   bl record
   bl check_vector_int_literal
   .int 0x28292A2B,0x38393A3B,0x2C2D2E2F,0x3C3D3E3F

   ########################################################################
   # Vector Processing Instructions: Logical bitwise operations
   ########################################################################

0: lvia %v27,0x55AA55AA

   # vand
0: vand %v3,%v27,%v24
   bl record
   bl check_vector_int_literal
   .int 0x55AA55AA & 0x20212223, 0x55AA55AA & 0x24252627
   .int 0x55AA55AA & 0x28292A2B, 0x55AA55AA & 0x2C2D2E2F

   # vandc
0: vandc %v3,%v27,%v24
   bl record
   bl check_vector_int_literal
   .int 0x55AA55AA & ~0x20212223, 0x55AA55AA & ~0x24252627
   .int 0x55AA55AA & ~0x28292A2B, 0x55AA55AA & ~0x2C2D2E2F

   # vnor
0: vnor %v3,%v27,%v24
   bl record
   bl check_vector_int_literal
   .int ~(0x55AA55AA | 0x20212223), ~(0x55AA55AA | 0x24252627)
   .int ~(0x55AA55AA | 0x28292A2B), ~(0x55AA55AA | 0x2C2D2E2F)

   # vor
0: vor %v3,%v27,%v24
   bl record
   bl check_vector_int_literal
   .int 0x55AA55AA | 0x20212223, 0x55AA55AA | 0x24252627
   .int 0x55AA55AA | 0x28292A2B, 0x55AA55AA | 0x2C2D2E2F

   # vxor
0: vxor %v3,%v27,%v24
   bl record
   bl check_vector_int_literal
   .int 0x55AA55AA ^ 0x20212223, 0x55AA55AA ^ 0x24252627
   .int 0x55AA55AA ^ 0x28292A2B, 0x55AA55AA ^ 0x2C2D2E2F

   # vsel
0: lvia %v4,0x66666666
   vsel %v3,%v27,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x11881188 | (0x20212223 & 0x66666666)
   .int 0x11881188 | (0x24252627 & 0x66666666)
   .int 0x11881188 | (0x28292A2B & 0x66666666)
   .int 0x11881188 | (0x2C2D2E2F & 0x66666666)

   ########################################################################
   # Vector Processing Instructions: Shift/rotate operations
   ########################################################################

   # vrlb
0: vrlb %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: vspltisb %v4,4
   vrlb %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x02122232,0x42526272,0x8292A2B2,0xC2D2E2F2
0: vrlb %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x20428819,0x42A48993,0x2852A859,0xC2A58B97

   # vrlh
0: vrlh %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: vspltisb %v4,12
   vrlh %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x12023222,0x52427262,0x9282B2A2,0xD2C2F2E2
0: vrlh %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x40421119,0x84A41393,0x52505951,0xA5859717

   # vrlw
0: vrlw %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: lvia %v4,20
   vrlw %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x22320212,0x62724252,0xA2B28292,0xE2F2C2D2
0: vrlw %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x01091119,0x12931392,0x49515941,0x97179616

   # vslb
0: vspltisb %v4,3
   vslb %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x00081018,0x20283038,0x40485058,0x60687078
0: vslb %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x20428818,0x40A08080,0x2852A858,0xC0A08080

   # vslh
0: vspltish %v4,3
   vslh %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x01081118,0x21283138,0x41485158,0x61687178
0: vslh %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x40421118,0x84A01380,0x52005800,0xA0008000

   # vslw
0: vspltisw %v4,3
   vslw %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x01091118,0x21293138,0x41495158,0x61697178
0: vslw %v3,%v24,%v24
   bl record
   bl check_vector_int_literal
   .int 0x01091118,0x12931380,0x49515800,0x97178000

   # vsl
0: vsl %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: vspltisb %v4,4
   vsl %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x02122232,0x42526272,0x8292A2B2,0xC2D2E2F0
0: vmr %v3,%v24
   vspltisb %v4,4
   vsl %v3,%v3,%v4
   bl record
   bl check_vector_int_literal
   .int 0x02122232,0x42526272,0x8292A2B2,0xC2D2E2F0

   # vslo
0: vslo %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: lvi %v4,75       # Low bits of the value should be ignored.
   vslo %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x292A2B2C,0x2D2E2F00,0x00000000,0x00000000
0: vmr %v3,%v24
   lvi %v4,24
   vslo %v3,%v3,%v4
   bl record
   bl check_vector_int_literal
   .int 0x23242526,0x2728292A,0x2B2C2D2E,0x2F000000

   # vsldoi
0: vsldoi %v3,%v24,%v26,0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: vsldoi %v3,%v24,%v26,13
   bl record
   bl check_vector_int_literal
   .int 0x2D2E2F80,0x81828384,0x85868788,0x898A8B8C
0: vmr %v3,%v24
   vsldoi %v3,%v3,%v26,13
   bl record
   bl check_vector_int_literal
   .int 0x2D2E2F80,0x81828384,0x85868788,0x898A8B8C
0: vmr %v3,%v26
   vsldoi %v3,%v24,%v3,13
   bl record
   bl check_vector_int_literal
   .int 0x2D2E2F80,0x81828384,0x85868788,0x898A8B8C

   # vsrb
0: vspltisb %v4,3
   vsrb %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0x10101010,0x10101010,0x11111111,0x11111111
0: vsrb %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0x80402010,0x08040201,0x88442211,0x08040201

   # vsrh
0: vspltish %v4,3
   vsrh %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0x10101050,0x109010D0,0x11111151,0x119111D1
0: vsrh %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0x40401050,0x0424010D,0x00440011,0x00040001

   # vsrw
0: vspltisw %v4,3
   vsrw %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0x10103050,0x1090B0D0,0x11113151,0x1191B1D1
0: vsrw %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0x10103050,0x01090B0D,0x00111131,0x0001191B

   # vsr
0: vsr %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: vspltisb %v4,4
   vsr %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x02021222,0x32425262,0x728292A2,0xB2C2D2E2
0: vmr %v3,%v24
   vspltisb %v4,4
   vsr %v3,%v3,%v4
   bl record
   bl check_vector_int_literal
   .int 0x02021222,0x32425262,0x728292A2,0xB2C2D2E2

   # vsro
0: vsro %v3,%v24,%v0
   bl record
   vmr %v4,%v24
   bl check_vector_int
0: lvi %v4,75       # Low bits of the value should be ignored.
   vsro %v3,%v24,%v4
   bl record
   bl check_vector_int_literal
   .int 0x00000000,0x00000000,0x00202122,0x23242526
0: vmr %v3,%v24
   lvi %v4,24
   vsro %v3,%v3,%v4
   bl record
   bl check_vector_int_literal
   .int 0x00000020,0x21222324,0x25262728,0x292A2B2C

   # vsrab
0: vspltisb %v4,3
   vsrab %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0xF0F0F0F0,0xF0F0F0F0,0xF1F1F1F1,0xF1F1F1F1
0: vsrab %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0x80C0E0F0,0xF8FCFEFF,0x88C4E2F1,0xF8FCFEFF

   # vsrah
0: vspltish %v4,3
   vsrah %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0xF010F050,0xF090F0D0,0xF111F151,0xF191F1D1
0: vsrah %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0xC040F050,0xFC24FF0D,0xFFC4FFF1,0xFFFCFFFF

   # vsraw
0: vspltisw %v4,3
   vsraw %v3,%v26,%v4
   bl record
   bl check_vector_int_literal
   .int 0xF0103050,0xF090B0D0,0xF1113151,0xF191B1D1
0: vsraw %v3,%v26,%v26
   bl record
   bl check_vector_int_literal
   .int 0xF0103050,0xFF090B0D,0xFFF11131,0xFFFF191B

   ########################################################################
   # Vector Processing Instructions: Pack/unpack operations
   ########################################################################

   # vpkuhum
0: vpkuhum %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0x21232527,0x292B2D2F,0x81838587,0x898B8D8F
   # Also check that "modulo"-type operations don't modify SAT.
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vpkuhum %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0x21232527,0x292B2D2F,0x81838587,0x898B8D8F
0: vmr %v3,%v26
   vpkuhum %v3,%v24,%v3
   bl record
   bl check_vector_int_nosat_literal
   .int 0x21232527,0x292B2D2F,0x81838587,0x898B8D8F

   # vpkuhus
0: vmrghb %v7,%v0,%v24
   vmrglb %v8,%v0,%v24
   vmrghb %v9,%v0,%v26
   vmrglb %v10,%v0,%v26
   vmrghb %v11,%v1,%v26
   vmrglb %v12,%v1,%v26
   vpkuhus %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
   # Check that saturating instructions do not clear SAT when no saturation.
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkuhus %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkuhus %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkuhus %v3,%v9,%v10
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkuhus %v3,%v11,%v12
   bl record
   vmr %v4,%v1
   bl check_vector_int_sat
   # Check that a value equal to the saturation limit is not treated as a
   # saturated value.
0: vmrghb %v4,%v0,%v1
   vpkuhus %v3,%v4,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vpkshus
0: vpkshus %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkshus %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkshus %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkshus %v3,%v9,%v10
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkshus %v3,%v11,%v12
   bl record
   vmr %v4,%v0
   bl check_vector_int_sat
0: vpkshus %v3,%v24,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_int_sat
0: vmrghb %v4,%v0,%v1
   vpkshus %v3,%v4,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vpkshss
0: vpkshss %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkshss %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkshss %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkshss %v3,%v9,%v10
   bl record
   lvia %v4,0x7F7F7F7F
   bl check_vector_int_sat
0: vpkshss %v3,%v11,%v12
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkshss %v3,%v26,%v26
   bl record
   lvia %v4,0x80808080
   bl check_vector_int_sat
0: lvia %v4,0x007FFF80
   vpkshss %v3,%v4,%v4
   bl record
   lvia %v4,0x7F807F80
   bl check_vector_int_nosat

   # vpkuwum
0: vpkuwum %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0x22232627,0x2A2B2E2F,0x82838687,0x8A8B8E8F
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vpkuwum %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0x22232627,0x2A2B2E2F,0x82838687,0x8A8B8E8F
0: vmr %v3,%v26
   vpkuwum %v3,%v24,%v3
   bl record
   bl check_vector_int_nosat_literal
   .int 0x22232627,0x2A2B2E2F,0x82838687,0x8A8B8E8F

   # vpkuwus
0: vmrghh %v7,%v0,%v24
   vmrglh %v8,%v0,%v24
   vmrghh %v9,%v0,%v26
   vmrglh %v10,%v0,%v26
   vmrghh %v11,%v1,%v26
   vmrglh %v12,%v1,%v26
   vpkuwus %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkuwus %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkuwus %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkuwus %v3,%v9,%v10
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkuwus %v3,%v11,%v12
   bl record
   vmr %v4,%v1
   bl check_vector_int_sat
0: vmrghh %v4,%v0,%v1
   vpkuwus %v3,%v4,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vpkswus
0: vpkswus %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkswus %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkswus %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkswus %v3,%v9,%v10
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkswus %v3,%v11,%v12
   bl record
   vmr %v4,%v0
   bl check_vector_int_sat
0: vpkswus %v3,%v24,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_int_sat
0: vmrghh %v4,%v0,%v1
   vpkswus %v3,%v4,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vpkswss
0: vpkswss %v3,%v7,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vpkswss %v3,%v3,%v8
   bl record
   vmr %v4,%v24
   bl check_vector_int_sat
0: vmr %v3,%v8
   vpkswss %v3,%v7,%v3
   bl record
   vmr %v4,%v24
   bl check_vector_int_nosat
0: vpkswss %v3,%v9,%v10
   bl record
   lvia %v4,0x7FFF7FFF
   bl check_vector_int_sat
0: vpkswss %v3,%v11,%v12
   bl record
   vmr %v4,%v26
   bl check_vector_int_nosat
0: vpkswss %v3,%v26,%v26
   bl record
   lvia %v4,0x80008000
   bl check_vector_int_sat
0: li %r3,0x7FFF
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   li %r3,-0x8000
   stw %r3,4(%r4)
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vpkswss %v3,%v4,%v4
   bl record
   lvia %v4,0x7FFF8000
   bl check_vector_int_nosat

   # vpkpx
0: lis %r3,0x29A7   # Just some random data for testing.
   ori %r3,%r3,0x0F11
   sldi %r3,%r3,32
   oris %r3,%r3,0x412E
   ori %r3,%r3,0xE4F5
   std %r3,0(%r4)
   not %r3,%r3
   std %r3,16(%r4)
   lis %r3,0x2109
   ori %r3,%r3,0xB6FE
   sldi %r3,%r3,32
   oris %r3,%r3,0xB5AC
   ori %r3,%r3,0xE7F6
   std %r3,8(%r4)
   not %r3,%r3
   std %r3,24(%r4)
   lv %v7,0,%r4
   lv %v8,16,%r4
   vpkpx %v3,%v7,%v8
   bl record
   bl check_vector_int_literal
   .int 0xD022979E,0x86DFD79E,0x2FDD6861,0x79202861
0: vmr %v3,%v7
   vpkpx %v3,%v3,%v8
   bl record
   bl check_vector_int_literal
   .int 0xD022979E,0x86DFD79E,0x2FDD6861,0x79202861
0: vmr %v3,%v8
   vpkpx %v3,%v7,%v3
   bl record
   bl check_vector_int_literal
   .int 0xD022979E,0x86DFD79E,0x2FDD6861,0x79202861

   # vupkhsb
0: vupkhsb %v3,%v26
   bl record
   bl check_vector_int_literal
   .int 0xFF80FF81,0xFF82FF83,0xFF84FF85,0xFF86FF87
0: vmr %v3,%v26
   vupkhsb %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0xFF80FF81,0xFF82FF83,0xFF84FF85,0xFF86FF87

   # vupklsb
0: vupklsb %v3,%v26
   bl record
   bl check_vector_int_literal
   .int 0xFF88FF89,0xFF8AFF8B,0xFF8CFF8D,0xFF8EFF8F
0: vmr %v3,%v26
   vupklsb %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0xFF88FF89,0xFF8AFF8B,0xFF8CFF8D,0xFF8EFF8F

   # vupkhsh
0: vupkhsh %v3,%v26
   bl record
   bl check_vector_int_literal
   .int 0xFFFF8081,0xFFFF8283,0xFFFF8485,0xFFFF8687
0: vmr %v3,%v26
   vupkhsh %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0xFFFF8081,0xFFFF8283,0xFFFF8485,0xFFFF8687

   # vupklsh
0: vupklsh %v3,%v26
   bl record
   bl check_vector_int_literal
   .int 0xFFFF8889,0xFFFF8A8B,0xFFFF8C8D,0xFFFF8E8F
0: vmr %v3,%v26
   vupklsh %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0xFFFF8889,0xFFFF8A8B,0xFFFF8C8D,0xFFFF8E8F

   # vupkhpx
0: vupkhpx %v3,%v7
   bl record
   bl check_vector_int_literal
   .int 0x000A0D07,0x00031811,0x0010090E,0xFF190715
0: vmr %v3,%v7
   vupkhpx %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0x000A0D07,0x00031811,0x0010090E,0xFF190715

   # vupklpx
0: vupklpx %v3,%v7
   bl record
   bl check_vector_int_literal
   .int 0x00080809,0xFF0D171E,0xFF0D0D0C,0xFF191F16
0: vmr %v3,%v7
   vupklpx %v3,%v3
   bl record
   bl check_vector_int_literal
   .int 0x00080809,0xFF0D171E,0xFF0D0D0C,0xFF191F16

   ########################################################################
   # Vector Processing Instructions: Integer compare
   ########################################################################

0: lis %r3,0x00FF
   ori %r3,%r3,0xFF00
   sldi %r3,%r3,32
   ori %r3,%r3,0xFFFF
   std %r3,0(%r4)
   lis %r3,0xFFFF
   stw %r3,8(%r4)
   li %r3,-1
   stw %r3,12(%r4)
   lv %v27,0,%r4
   vsel %v28,%v26,%v24,%v27  # V28 = 0x80212283_84852627_28298A8B_2C2D2E2F

   # vcmpequb/vcmpequb.
0: vcmpequb. %v3,%v28,%v24
   bl record
   vmr %v4,%v27
   bl check_vector_compare_some
0: vcmpequb. %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpequb. %v3,%v24,%v26
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpequb %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some  # CR6 should not have been written.

   # vcmpequh/vcmpequh.
0: vcmpequh. %v3,%v28,%v24
   bl record
   vsldoi %v4,%v27,%v0,4
   vsldoi %v4,%v0,%v4,12
   bl check_vector_compare_some
0: vcmpequh. %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpequh. %v3,%v24,%v26
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpequh %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpequw/vcmpequw.
0: vcmpequw. %v3,%v28,%v24
   bl record
   vsldoi %v4,%v0,%v1,4
   bl check_vector_compare_some
0: vcmpequw. %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpequw. %v3,%v24,%v26
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpequw %v3,%v24,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtub/vcmpgtub.
0: lvia %v7,0x80808080
   vcmpgtub. %v3,%v7,%v28
   bl record
   vmr %v4,%v27
   bl check_vector_compare_some
0: vcmpgtub. %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtub. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtub %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtuh/vcmpgtuh.
0: lvia %v7,0x80218021
   vcmpgtuh. %v3,%v7,%v28
   bl record
   vsldoi %v4,%v27,%v0,4
   vsldoi %v4,%v1,%v4,12
   vsldoi %v4,%v4,%v0,2
   vsldoi %v4,%v0,%v4,14
   bl check_vector_compare_some
0: vcmpgtuh. %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtuh. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtuh %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtuw/vcmpgtuw.
0: lvia %v7,0x80212283
   vcmpgtuw. %v3,%v7,%v28
   bl record
   vsldoi %v4,%v0,%v1,8
   bl check_vector_compare_some
0: vcmpgtuw. %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtuw. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtuw %v3,%v26,%v24
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtsb/vcmpgtsb.
0: lvia %v7,0x21212121
   vcmpgtsb. %v3,%v7,%v28
   bl record
   vnot %v4,%v27
   bl check_vector_compare_some
0: vcmpgtsb. %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtsb. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtsb %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtsh/vcmpgtsh.
0: lvia %v7,0x22832283
   vcmpgtsh. %v3,%v7,%v28
   bl record
   vsldoi %v4,%v27,%v0,4
   vsldoi %v4,%v1,%v4,12
   vsldoi %v4,%v4,%v0,2
   vsldoi %v4,%v0,%v4,14
   vnot %v4,%v4
   bl check_vector_compare_some
0: vcmpgtsh. %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtsh. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtsh %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   # vcmpgtsw/vcmpgtsw.
0: lvia %v7,0x28298A8B
   vcmpgtsw. %v3,%v7,%v28
   bl record
   vsldoi %v4,%v1,%v0,8
   bl check_vector_compare_some
0: vcmpgtsw. %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgtsw. %v3,%v24,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none
0: vcmpgtsw %v3,%v24,%v26
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some

   ########################################################################
   # Vector Processing Instructions: Integer maximum/minimum
   ########################################################################

   # vmaxub
0: lvia %v7,0x40404040
   vmaxub %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80404083,0x84854040,0x40408A8B,0x40404040

   # vmaxuh
0: vmaxuh %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80214040,0x84854040,0x40408A8B,0x40404040

   # vmaxuw
0: vmaxuw %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80212283,0x84852627,0x40404040,0x40404040

   # vmaxsb
0: vmaxsb %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x00212200,0x00002627,0x28290000,0x2C2D2E2F

   # vmaxsh
0: vmaxsh %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x00002283,0x00002627,0x28290000,0x2C2D2E2F

   # vmaxsw
0: vmaxsw %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x00000000,0x00000000,0x28298A8B,0x2C2D2E2F

   # vminub
0: vminub %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x40212240,0x40402627,0x28294040,0x2C2D2E2F

   # vminuh
0: vminuh %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x40402283,0x40402627,0x28294040,0x2C2D2E2F

   # vminuw
0: vminuw %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x40404040,0x40404040,0x28298A8B,0x2C2D2E2F

   # vminsb
0: vminsb %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80000083,0x84850000,0x00008A8B,0x00000000

   # vminsh
0: vminsh %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80210000,0x84850000,0x00008A8B,0x00000000

   # vminsw
0: vminsw %v3,%v0,%v28
   bl record
   bl check_vector_int_literal
   .int 0x80212283,0x84852627,0x00000000,0x00000000

   ########################################################################
   # Vector Processing Instructions: Integer addition
   ########################################################################

   # vaddubm
0: vaddubm %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvi %v3,1
   mtvscr %v3
   vaddubm %v3,%v26,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0x00020406,0x080A0C0E,0x10121416,0x181A1C1E
0: vmr %v3,%v26
   vaddubm %v3,%v3,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00020406,0x080A0C0E,0x10121416,0x181A1C1E

   # vadduhm
0: vadduhm %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvi %v3,1
   mtvscr %v3
   vadduhm %v3,%v26,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0x01020506,0x090A0D0E,0x11121516,0x191A1D1E
0: vmr %v3,%v26
   vadduhm %v3,%v3,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0x01020506,0x090A0D0E,0x11121516,0x191A1D1E

   # vadduwm
0: vadduhm %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvi %v3,1
   mtvscr %v3
   vadduhm %v3,%v26,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0x01020506,0x090A0D0E,0x11121516,0x191A1D1E
0: vmr %v3,%v26
   vadduhm %v3,%v3,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0x01020506,0x090A0D0E,0x11121516,0x191A1D1E

   # vaddubs
0: vaddubs %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vaddubs %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: vaddubs %v3,%v26,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xFFA2A4FF,0xFFFFACAE,0xB0B2FFFF,0xB8BABCBE
0: vspltisb %v3,1
   vspltisb %v4,-2
   vaddubs %v3,%v3,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vadduhs
0: vmrghb %v4,%v24,%v1  # Force carries to verify operation element size.
   vadduhs %v3,%v4,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA180A482,0xA784AA86,0xAD88B08A,0xB38CB68E
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vadduhs %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: vadduhs %v3,%v26,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xFFFFA506,0xFFFFACAE,0xB0B2FFFF,0xB8BABCBE
0: vspltish %v3,1
   vspltish %v4,-2
   vaddubs %v3,%v3,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vadduws
0: vmrghh %v4,%v24,%v1
   vadduws %v3,%v4,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A38282,0xA6A98686,0xACAF8A8A,0xB2B58E8E
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vadduws %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: vadduws %v3,%v26,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xFFFFFFFF,0xFFFFFFFF,0xB0B31516,0xB8BABCBE
0: vspltisw %v3,1
   vspltisw %v4,-2
   vaddubs %v3,%v3,%v4
   bl record
   vmr %v4,%v1
   bl check_vector_int_nosat

   # vaddsbs
0: vaddsbs %v3,%v24,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vaddsbs %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvia %v3,0x78887888
   vaddsbs %v3,%v3,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xF8A97F80,0xFC807FAF,0x7FB10280,0x7FB57FB7
0: lvia %v3,0x7E817E81
   lvia %v4,0x01FF01FF
   vaddsbs %v3,%v3,%v4
   bl record
   lvia %v4,0x7F807F80
   bl check_vector_int_nosat

   # vaddshs
0: vmrghb %v4,%v24,%v1
   vaddshs %v3,%v4,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA180A482,0xA784AA86,0xAD88B08A,0xB38CB68E
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vaddshs %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lvia %v3,0x78888888
   vaddshs %v3,%v3,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xF8A9AB0B,0xFD0DAEAF,0x7FFF8000,0x7FFFB6B7
0: lvia %v3,0x7FFE8001
   lvia %v4,0x0001FFFF
   vaddshs %v3,%v3,%v4
   bl record
   lvia %v4,0x7FFF8000
   bl check_vector_int_nosat

   # vaddsws
0: vmrghh %v4,%v24,%v1
   vaddsws %v3,%v4,%v26
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA0A38282,0xA6A98686,0xACAF8A8A,0xB2B58E8E
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v24
   vaddsws %v3,%v3,%v26
   bl record
   bl check_vector_int_sat_literal
   .int 0xA0A2A4A6,0xA8AAACAE,0xB0B2B4B6,0xB8BABCBE
0: lis %r3,0x7888
   ori %r3,%r3,0x8888
   sldi %r3,%r3,32
   oris %r3,%r3,0x8888
   ori %r3,%r3,0x8888
   std %r3,0(%r4)
   std %r3,8(%r4)
   lv %v3,0,%r4
   vaddsws %v3,%v3,%v28
   bl record
   bl check_vector_int_sat_literal
   .int 0xF8A9AB0B,0x80000000,0x7FFFFFFF,0xB4B5B6B7
0: lis %r3,0x7FFF
   ori %r3,%r3,0xFFFE
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   not %r3,%r3      # 0x80000001
   stw %r3,4(%r4)
   stw %r3,12(%r4)
   li %r3,1
   stw %r3,16(%r4)
   stw %r3,24(%r4)
   li %r3,-1
   stw %r3,20(%r4)
   stw %r3,28(%r4)
   lv %v3,0,%r4
   lv %v4,16,%r4
   vaddsws %v3,%v3,%v4
   bl record
   bl check_vector_int_nosat_literal
   .int 0x7FFFFFFF,0x80000000,0x7FFFFFFF,0x80000000

   # vaddcuw
0: vaddcuw %v3,%v26,%v28
   bl record
   bl check_vector_int_literal
   .int 1,1,0,0

   ########################################################################
   # Vector Processing Instructions: Integer subtraction
   ########################################################################

   # vsububm
0: lvia %v7,0xC0C0C0C0
   lvia %v8,0x40404040
   vsububm %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsububm %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsububm %v3,%v24,%v8
   bl record
   lv %v4,0x1E0,%r4
   bl check_vector_int_nosat

   # vsubuhm
0: vsubuhm %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubuhm %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsubuhm %v3,%v24,%v8
   bl record
   lv %v4,0x1E0,%r4
   bl check_vector_int_nosat_literal
   .int 0xDFE1E1E3,0xE3E5E5E7,0xE7E9E9EB,0xEBEDEDEF

   # vsubuwm
0: vsubuwm %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubuwm %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsubuwm %v3,%v24,%v8
   bl record
   lv %v4,0x1E0,%r4
   bl check_vector_int_nosat_literal
   .int 0xDFE0E1E3,0xE3E4E5E7,0xE7E8E9EB,0xEBECEDEF

   # vsububs
0: vsububs %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsububs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsububs %v3,%v28,%v8
   bl record
   bl check_vector_int_sat_literal
   .int 0x40000043,0x44450000,0x00004A4B,0x00000000

   # vsubuhs
0: vsubuhs %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubuhs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsubuhs %v3,%v28,%v8
   bl record
   bl check_vector_int_sat_literal
   .int 0x3FE10000,0x44450000,0x00004A4B,0x00000000

   # vsubuws
0: vsubuws %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubuws %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: vsubuws %v3,%v28,%v8
   bl record
   bl check_vector_int_sat_literal
   .int 0x3FE0E243,0x4444E5E7,0x00000000,0x00000000

   # vsubsbs
0: vsubsbs %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubsbs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvia %v3,0x78887888
   vsubsbs %v3,%v28,%v3
   bl record
   bl check_vector_int_sat_literal
   .int 0x807FAAFB,0x80FDAE7F,0xB07F8003,0xB47FB67F

   # vsubshs
0: vsubshs %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubshs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvia %v3,0x78888888
   vsubshs %v3,%v28,%v3
   bl record
   bl check_vector_int_sat_literal
   .int 0x80007FFF,0x80007FFF,0xAFA10203,0xB3A57FFF

   # vsubsws
0: vsubsws %v3,%v7,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v7
   vsubsws %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0xA09F9E9D,0x9C9B9A99,0x98979695,0x94939291
0: lis %r3,0x7888
   ori %r3,%r3,0x8888
   sldi %r3,%r3,32
   oris %r3,%r3,0x8888
   ori %r3,%r3,0x8888
   std %r3,0(%r4)
   std %r3,8(%r4)
   lv %v3,0,%r4
   vsubsws %v3,%v28,%v3
   bl record
   bl check_vector_int_sat_literal
   .int 0x80000000,0xFBFC9D9F,0xAFA10203,0x7FFFFFFF

   # vsubcuw
0: lvia %v3,0x40404040
   vsubcuw %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0,0,0,1

   ########################################################################
   # Vector Processing Instructions: Integer multiplication
   ########################################################################

   # vmuleub
0: vmuleub %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x10000484,0x129005A4,0x064016A4,0x07900844

   # vmuleuh
0: vmuleuh %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x1014A441,0x12B5DB39,0x064CD691,0x079F7FE9

   # vmulesb
0: vmulesb %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0xF0000484,0xEE9005A4,0x0640ECA4,0x07900844

   # vmulesh
0: vmulesh %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0xEFF3A441,0xEE90DB39,0x064CD691,0x079F7FE9

   # vmuloub
0: vmuloub %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x044111E9,0x133905F1,0x06911759,0x07E908A1

   # vmulouh
0: vmulouh %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x049A1DE9,0x05AF99F1,0x16D21359,0x0854ECA1

   # vmulosb
0: vmulosb %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x0441EEE9,0xEE3905F1,0x0691EC59,0x07E908A1

   # vmulosh
0: vmulosh %v3,%v24,%v28
   bl record
   bl check_vector_int_literal
   .int 0x049A1DE9,0x05AF99F1,0xECA71359,0x0854ECA1

   ########################################################################
   # Vector Processing Instructions: Integer average
   ########################################################################

   # vavgub
0: lvia %v7,0x41404040  # Chosen so the byte/halfword/word results all differ.
   vavgub %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x61313162,0x63633334,0x35356566,0x37373738

   # vavguh
0: vavguh %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x60B13162,0x62E33334,0x34B56566,0x36B73738

   # vavguw
0: vavguw %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0x60B0B162,0x62E2B334,0x34B4E566,0x36B6B738

   # vavgsb
0: vavgsb %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0xE13131E2,0xE3E33334,0x3535E5E6,0x37373738

   # vavgsh
0: vavgsh %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0xE0B13162,0xE2E33334,0x34B5E566,0x36B73738

   # vavgsw
0: vavgsw %v3,%v7,%v28
   bl record
   bl check_vector_int_literal
   .int 0xE0B0B162,0xE2E2B334,0x34B4E566,0x36B6B738

   ########################################################################
   # Vector Processing Instructions: Integer horizontal sum
   ########################################################################

   # vsum4ubs
0: vsum4ubs %v3,%v28,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0x20212369,0x2425277D,0x28292B91,0x2C2D2EE5
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vsum4ubs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0x20212369,0x2425277D,0x28292B91,0x2C2D2EE5
0: lvia %v4,0xFFFFFF00
   vsum4ubs %v3,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFFF,0xFFFFFFB6
0: lvia %v5,0xFFFFFE99
   vsum4ubs %v3,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0xFFFFFFDF,0xFFFFFFEF,0xFFFFFFFF,0xFFFFFF4F

   # vsum4sbs
0: vsum4sbs %v3,%v28,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0x20212169,0x2425257D,0x28292991,0x2C2D2EE5
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vsum4sbs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0x20212169,0x2425257D,0x28292991,0x2C2D2EE5
0: lis %r3,0x8000
   ori %r3,%r3,0x80
   stw %r3,0(%r4)
   # This value (0x80000100) will cause signed underflow after two
   # additions, which will cause the test to fail if the implementation
   # saturates after each addition instead of at the end.  We use two
   # copies to handle implementations which add from the low or high byte
   # of each word.
   lis %r3,0x8000
   ori %r3,%r3,0x100
   stw %r3,4(%r4)
   stw %r3,8(%r4)
   lis %r3,0x7FFF
   ori %r3,%r3,0xFF80
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vsum4sbs %v3,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x80000000,0x80000056,0x80000066,0x7FFFFFFF
0: std %r0,0(%r4)
   lis %r3,0x8000
   ori %r3,%r3,0x009A
   stw %r3,8(%r4)
   lis %r3,0x7FFF
   ori %r3,%r3,0xFF49
   stw %r3,12(%r4)
   lv %v5,0,%r4
   vsum4sbs %v3,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0xFFFFFF46,0xFFFFFF56,0x80000000,0x7FFFFFFF

   # vsum4shs
0: vsum4shs %v3,%v28,%v24
   bl record
   bl check_vector_int_nosat_literal
   .int 0x2020C4C7,0x2424D0D3,0x2828DCDF,0x2C2D888B
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vsum4shs %v3,%v3,%v24
   bl record
   bl check_vector_int_sat_literal
   .int 0x2020C4C7,0x2424D0D3,0x2828DCDF,0x2C2D888B
0: lis %r3,0x8000
   ori %r3,%r3,0x80
   stw %r3,0(%r4)
   lis %r3,0x8000  # Similar logic to the third vsum4sbs test above.
   ori %r3,%r3,0x6000
   stw %r3,4(%r4)
   stw %r3,8(%r4)
   lis %r3,0x7FFF
   ori %r3,%r3,0xFF80
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vsum4shs %v3,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x80000000,0x80000AAC,0x800012B4,0x7FFFFFFF
0: std %r0,0(%r4)
   lis %r3,0x8000
   ori %r3,%r3,0x4D4C
   stw %r3,8(%r4)
   lis %r3,0x7FFF
   ori %r3,%r3,0xA5A3
   stw %r3,12(%r4)
   lv %v5,0,%r4
   vsum4shs %v3,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0xFFFFA2A4,0xFFFFAAAC,0x80000000,0x7FFFFFFF

   # vsum2sws
0: lis %r3,0x8000
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   lis %r3,0x7FFF
   stw %r3,4(%r4)
   lis %r3,0x2000
   stw %r3,12(%r4)
   lv %v7,0,%r4
   vsum2sws %v3,%v28,%v7
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x84A548AA,0x00000000,0x7456B8BA
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vsum2sws %v3,%v3,%v7
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x84A548AA,0x00000000,0x7456B8BA
0: lvia %v4,0x40000000
   vsum2sws %v3,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x80000000,0x00000000,0x7FFFFFFF
0: lis %r3,0x4000
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   lis %r3,0xC000
   stw %r3,4(%r4)
   stw %r3,12(%r4)
   lv %v3,0,%r4
   stw %r0,0(%r4)
   stw %r0,8(%r4)
   lis %r3,0x6000
   stw %r3,4(%r4)
   lis %r3,0xA000
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vsum2sws %v3,%v3,%v4
   bl record
   bl check_vector_int_nosat
0: lis %r3,0x7B59
   ori %r3,%r3,0xB756
   stw %r3,4(%r4)
   lis %r3,0x2BA9
   ori %r3,%r3,0x4745
   stw %r3,12(%r4)
   lv %v5,0,%r4
   vsum2sws %v3,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x80000000,0x00000000,0x7FFFFFFF

   # vsumsws
0: lis %r3,0x8000
   stw %r3,0(%r4)
   stw %r3,4(%r4)
   stw %r3,8(%r4)
   lis %r3,0x4000
   stw %r3,12(%r4)
   lv %v7,0,%r4
   vsumsws %v3,%v28,%v7
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x00000000,0x00000000,0x98FD0164
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vsumsws %v3,%v3,%v7
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x00000000,0x00000000,0x98FD0164
0: lvi %v4,0x20000000
   vsumsws %v3,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x00000000,0x00000000,0x80000000
0: lvia %v3,0x10000000
   lvi %v4,0x40000000
   vsumsws %v3,%v3,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x00000000,0x00000000,0x7FFFFFFF
0: lvia %v3,0x10000000
   lvi %v5,0x3FFFFFFF
   vsumsws %v3,%v3,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x00000000,0x00000000,0x7FFFFFFF
0: lvia %v3,0xF0000000
   lvi %v6,0xC0000000
   vsumsws %v3,%v3,%v6
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x00000000,0x00000000,0x80000000

   ########################################################################
   # Vector Processing Instructions: Integer multiply-add
   ########################################################################

   # vmladduhm
0: vmladduhm %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0xD472501C,0x0F6ED028,0x0ECA4D94,0xBC262AE0
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmladduhm %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0xD472501C,0x0F6ED028,0x0ECA4D94,0xBC262AE0

   # vmhaddshs
0: vmhaddshs %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x10183B67,0x11564196,0x44D21389,0x4B7B4EE8
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmhaddshs %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x10183B67,0x11564196,0x44D21389,0x4B7B4EE8
0: lvia %v4,0x78888888
   vmhaddshs %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x586F91BC,0x55A993E7,0x7FFF8000,0x7FFF9931
0: lvia %v5,0xA2DF6F56
   vmhaddshs %v3,%v24,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0x82C6788A,0x80007AB5,0xAF7848A4,0xB21D7FFF

   # vmhraddshs
0: vmhraddshs %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x10183B67,0x11574196,0x44D31389,0x4B7C4EE9
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmhraddshs %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x10183B67,0x11574196,0x44D31389,0x4B7C4EE9
0: lvia %v4,0x78888888
   vmhraddshs %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x586F91BC,0x55AA93E7,0x7FFF8000,0x7FFF9932
0: lvia %v5,0xA2DE6F55
   vmhraddshs %v3,%v24,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0x82C57889,0x80007AB4,0xAF7848A3,0xB21D7FFF

   ########################################################################
   # Vector Processing Instructions: Integer mixed-size multiply-add
   ########################################################################

   # vmsumubm
0: vmsumubm %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x30315CE1,0x34356795,0x38397509,0x3C3D5E9D
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsumubm %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x30315CE1,0x34356795,0x38397509,0x3C3D5E9D
0: lvia %v4,0xFFFFFF00
   vmsumubm %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_nosat_literal
   .int 0x000029AE,0x0000305E,0x000039CE,0x00001F5E

   # vmsumuhm
0: vmsumuhm %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x44DFF45D,0x4C9AAB61,0x55582425,0x4C31AAC9
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsumuhm %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x44DFF45D,0x4C9AAB61,0x55582425,0x4C31AAC9
0: lvia %v4,0xE8000000
   vmsumuhm %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_nosat_literal
   .int 0xFCAEC22A,0x0065752A,0x051EE9EA,0xF7F46C8A

   # vmsumuhs
0: vmsumuhs %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x44DFF45D,0x4C9AAB61,0x55582425,0x4C31AAC9
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsumuhs %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x44DFF45D,0x4C9AAB61,0x55582425,0x4C31AAC9
0: lvia %v4,0xE8000000
   vmsumuhs %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0xFCAEC22A,0xFFFFFFFF,0xFFFFFFFF,0xF7F46C8A
0: lvia %v5,0xE2E11615
   vmsumuhs %v3,%v24,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0xF78FD83F,0xFB468B3F,0xFFFFFFFF,0xF2D5829F

   # vmsummbm
0: vmsummbm %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x30315CE1,0x34356795,0x38397509,0x3C3D5E9D
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsummbm %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x30315CE1,0x34356795,0x38397509,0x3C3D5E9D
0: lvia %v4,0xFFFFFF00
   vmsumubm %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_nosat_literal
   .int 0x000029AE,0x0000305E,0x000039CE,0x00001F5E
0: vmsummbm %v3,%v28,%v24,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x303119E1,0x34351E95,0x38392009,0x3C3D5E9D

   # vmsumshm
0: vmsumshm %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x24BEF45D,0x2875AB61,0x2B2D2425,0x4C31AAC9
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsumshm %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x24BEF45D,0x2875AB61,0x2B2D2425,0x4C31AAC9
0: lis %r3,0x8C80
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   lis %r3,0x7380
   stw %r3,4(%r4)
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vmsumshm %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_nosat_literal
   .int 0x810DC22A,0x67C0752A,0x7F73E9EA,0x83746C8A

   # vmsumshs
0: vmsumshs %v3,%v24,%v28,%v25
   bl record
   bl check_vector_int_nosat_literal
   .int 0x24BEF45D,0x2875AB61,0x2B2D2425,0x4C31AAC9
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v28
   vmsumshs %v3,%v24,%v3,%v25
   bl record
   bl check_vector_int_sat_literal
   .int 0x24BEF45D,0x2875AB61,0x2B2D2425,0x4C31AAC9
0: lis %r3,0x8C80
   stw %r3,0(%r4)
   stw %r3,8(%r4)
   lis %r3,0x7380
   stw %r3,4(%r4)
   stw %r3,12(%r4)
   lv %v4,0,%r4
   vmsumshs %v3,%v24,%v28,%v4
   bl record
   bl check_vector_int_sat_literal
   .int 0x810DC22A,0x67C0752A,0x80000000,0x7FFFFFFF
0: lis %r3,0x8D0C
   ori %r3,%r3,0x1616
   stw %r3,8(%r4)
   lis %r3,0x700B
   ori %r3,%r3,0x9375
   stw %r3,12(%r4)
   lv %v5,0,%r4
   vmsumshs %v3,%v24,%v28,%v5
   bl record
   bl check_vector_int_nosat_literal
   .int 0x810DC22A,0x67C0752A,0x80000000,0x7FFFFFFF

   ########################################################################
   # Vector Processing Instructions: Floating-point compare
   ########################################################################

0: bl 1f
1: mflr %r31
   addi %r31,%r31,2f-1b
   lv %v24,0,%r31
   lv %v25,16,%r31
   lv %v26,32,%r31
   lv %v27,48,%r31
   lv %v28,64,%r31
   lv %v29,80,%r31
   vspltw %v7,%v27,0  # 0x80000000 x 4
   b 0f
   .balign 16
2: .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
   .int 0x00000001,0xBF800000,0x40000000,0x40800000
   .int 0x00800000,0x80800000,0x41000000,0x41800000
   .int 0x80000000,0x3F000000,0x7F800000,0x7F900000
   .int 0x3F800000,0x40000000,0x40400000,0x40800000
   .int 0xBF800000,0xC0000000,0x80000000,0xFFF00000

   # vcmpeqfp/vcmpeqfp.
0: vcmpeqfp %v3,%v25,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some
0: vcmpeqfp %v3,%v24,%v24
   bl record
   vsldoi %v4,%v1,%v0,4
   bl check_vector_compare_some
0: lvia %v9,0x80000000
   vxor %v3,%v24,%v9
   vcmpeqfp. %v3,%v24,%v3
   bl record
   vsldoi %v4,%v1,%v0,12
   bl check_vector_compare_some
0: vcmpeqfp. %v3,%v25,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpeqfp. %v3,%v24,%v25
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none

   # vcmpgefp/vcmpgefp.
0: vcmpgefp %v3,%v25,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some
0: vcmpgefp %v3,%v24,%v24
   bl record
   vsldoi %v4,%v1,%v0,4
   bl check_vector_compare_some
0: vxor %v3,%v24,%v9
   vcmpgefp. %v3,%v3,%v24
   bl record
   vsldoi %v4,%v1,%v0,12
   bl check_vector_compare_some
0: vcmpgefp. %v3,%v25,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vcmpgefp. %v3,%v25,%v26
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none

   # vcmpgtfp/vcmpgtfp.
0: vcmpgtfp %v3,%v26,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_some
0: vcmpgtfp. %v3,%v24,%v25
   bl record
   vsldoi %v4,%v0,%v1,8
   vsldoi %v4,%v4,%v0,4
   bl check_vector_compare_some
0: vcmpgtfp. %v3,%v26,%v25
   bl record
   vmr %v4,%v1
   bl check_vector_compare_all
0: vsldoi %v3,%v26,%v0,4
   vsldoi %v3,%v0,%v3,12
   vcmpgtfp. %v3,%v3,%v24
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none

   # vcmpbfp/vcmpbfp.
0: vspltw %v11,%v26,3
   lvia %v8,0xC0000000
   lvia %v10,0x40000000
   vcmpbfp %v3,%v26,%v11
   bl record
   vmr %v4,%v0
   bl check_vector_compare_some
0: vcmpbfp. %v3,%v26,%v11
   bl record
   vmr %v4,%v0
   bl check_vector_compare_none  # vcmpbfp sets the "none" bit for "all".
0: vspltw %v3,%v24,3
   vcmpbfp. %v3,%v3,%v3
   bl record
   vmr %v4,%v8
   bl check_vector_compare_some  # No bits set in CR for "none in bounds".
0: vcmpbfp. %v3,%v25,%v26
   bl record
   vsldoi %v4,%v0,%v10,4
   vsldoi %v4,%v4,%v0,8
   bl check_vector_compare_some
0: vcmpbfp. %v3,%v25,%v24
   bl record
   vsldoi %v4,%v9,%v0,8
   vsldoi %v4,%v4,%v8,4
   bl check_vector_compare_some
0: vxor %v3,%v25,%v9
   vcmpbfp. %v3,%v3,%v24
   bl record
   vsldoi %v4,%v10,%v0,8
   vsldoi %v4,%v4,%v8,4
   bl check_vector_compare_some

   ########################################################################
   # Vector Processing Instructions: Floating-point maximum/minimum
   ########################################################################

   # vmaxfp
0: vmaxfp %v3,%v25,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000001,0x3F000000,0x7F800000,0x7FD00000
0: vmaxfp %v3,%v27,%v25
   bl record
   bl check_vector_float_literal
   .int 0x00000001,0x3F000000,0x7F800000,0x7FD00000
0: vmaxfp %v3,%v24,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
0: vmaxfp %v3,%v27,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FD00000

   # vminfp
0: vminfp %v3,%v25,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0x40000000,0x7FD00000
0: vminfp %v3,%v27,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0x40000000,0x7FD00000
0: vminfp %v3,%v24,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x3F000000,0x7F800000,0x7FE00000
0: vminfp %v3,%v27,%v24
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x3F000000,0x7F800000,0x7FD00000

   ########################################################################
   # Vector Processing Instructions: Floating-point arithmetic
   ########################################################################

0: bl 1f
1: mflr %r31
   addi %r31,%r31,2f-1b
   lv %v30,0,%r31
   lv %v31,16,%r31
   lv %v10,32,%r31
   b 0f
   .balign 16
2: .int 0x3FB33333,0x3FB33333,0x40866666,0x00000000
   .int 0x40400000,0x40400000,0x3F800000,0x00000000
   .int 0x00000000,0x34400000,0x34400000,0x00000000

   # vaddfp
0: vaddfp %v3,%v25,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000001,0xBF000000,0x7F800000,0x7FD00000
0: vaddfp %v3,%v27,%v25
   bl record
   bl check_vector_float_literal
   .int 0x00000001,0xBF000000,0x7F800000,0x7FD00000
0: vaddfp %v3,%v24,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3FC00000,0x7F800000,0x7FE00000
0: vaddfp %v3,%v27,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3FC00000,0x7F800000,0x7FD00000
0: vxor %v3,%v24,%v7
   vaddfp %v3,%v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF000000,0x7FC00000,0xFFE00000

   # vsubfp
0: vsubfp %v3,%v25,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000001,0xBFC00000,0xFF800000,0x7FD00000
0: vsubfp %v3,%v27,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000001,0x3FC00000,0x7F800000,0x7FD00000
0: vsubfp %v3,%v27,%v24
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF000000,0x7FC00000,0x7FD00000
0: vxor %v3,%v24,%v7
   vsubfp %v3,%v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0xBFC00000,0xFF800000,0xFFE00000

   # vmaddfp
0: vmaddfp %v3,%v25,%v28,%v26
   bl record
   bl check_vector_float_literal
   .int 0x00800001,0xC0000000,0x41600000,0x42000000
   # Check various invalid operations.
0: vmaddfp %v3,%v24,%v29,%v27  # infinity * 0
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBFC00000,0x7FC00000,0x7FE00000
0: vmaddfp %v3,%v29,%v24,%v27  # 0 * infinity
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBFC00000,0x7FC00000,0xFFF00000
0: vxor %v8,%v27,%v7
   vmaddfp %v3,%v24,%v25,%v8   # +infinity * +normal + -infinity
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0xBFC00000,0x7FC00000,0x7FE00000
0: vxor %v9,%v25,%v7
   vmaddfp %v3,%v9,%v24,%v27   # -normal * +infinity + +infinity
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x3FC00000,0x7FC00000,0x7FD00000
   # Check that NaNs are chosen in the right order (VA -> VB -> VC).
   # Remember that the operand order is: vmaddfp VD,VA,VC,VB
0: vmaddfp %v3,%v28,%v29,%v27
   bl record
   bl check_vector_float_literal
   .int 0xBF800000,0xC0600000,0x7F800000,0x7FD00000
0: vmaddfp %v3,%v28,%v29,%v28
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0xC0000000,0x40400000,0xFFF00000
   # Check that the product is not rounded.
0: vmaddfp %v3,%v30,%v31,%v10
   bl record
   bl check_vector_float_literal
   .int 0x40866666,0x40866667,0x40866666,0x00000000

   # vnmsubfp
0: vnmsubfp %v3,%v25,%v28,%v26
   bl record
   bl check_vector_float_literal
   .int 0x007FFFFF,0x40000000,0x40000000,0x80000000
0: vnmsubfp %v3,%v24,%v29,%v27  # infinity * 0
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x40200000,0x7FC00000,0x7FE00000
0: vnmsubfp %v3,%v29,%v24,%v27  # 0 * infinity
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x40200000,0x7FC00000,0xFFF00000
0: vnmsubfp %v3,%v24,%v25,%v27  # +infinity * +normal - +infinity
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x3FC00000,0x7FC00000,0x7FE00000
0: vnmsubfp %v3,%v9,%v24,%v8    # -normal * +infinity - -infinity
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0xBFC00000,0x7FC00000,0xFFD00000
0: vnmsubfp %v3,%v28,%v29,%v27
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x40900000,0x7F800000,0x7FD00000
0: vnmsubfp %v3,%v28,%v29,%v28
   bl record
   bl check_vector_float_literal
   .int 0x40000000,0x40C00000,0x40400000,0xFFF00000

   # vexptefp
0: vexptefp %v3,%v24
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x40000000,0x7F800000,0x7FE00000
0: vxor %v3,%v24,%v7
   vexptefp %v3,%v3
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x3F000000,0x00000000,0xFFE00000

   # vlogefp
0: vlogefp %v3,%v25
   bl record
   bl check_vector_float_literal
   .int 0xC3150000,0x7FC00000,0x3F800000,0x40000000

   # vrefp
0: vrefp %v3,%v27
   bl record
   bl check_vector_float_bounds_literal
   .int 0xFF800000,0x3FFFF000,0x00000000,0x7FD00000
   .int 0xFF800000,0x40000800,0x00000000,0x7FD00000
0: vxor %v3,%v27,%v7
   vrefp %v3,%v3
   bl record
   bl check_vector_float_bounds_literal
   .int 0x7F800000,0xBFFFF000,0x80000000,0xFFD00000
   .int 0x7F800000,0xC0000800,0x80000000,0xFFD00000

   # vrsqrtefp
0: vrsqrtefp %v3,%v25
   bl record
   bl check_vector_float_bounds_literal
   .int 0x64B4F942,0x7FC00000,0x3F34F942,0x3EFFC000
   .int 0x64B51044,0x7FC00000,0x3F351044,0x3F002000
0: vrsqrtefp %v3,%v27
   bl record
   bl check_vector_float_bounds_literal
   .int 0xFF800000,0x3FB4F942,0x00000000,0x7FD00000
   .int 0xFF800000,0x3FB51044,0x00000000,0x7FD00000

   ########################################################################
   # Vector Processing Instructions: Floating-point / integer conversion
   ########################################################################

0: bl 1f
1: mflr %r31
   addi %r31,%r31,2f-1b
   lv %v24,0,%r31
   vxor %v25,%v24,%v7
   lv %v26,16,%r31
   vxor %v27,%v26,%v7
   lv %v28,32,%r31
   lv %v29,48,%r31
   lv %v30,64,%r31
   lv %v31,80,%r31
   b 0f
   .balign 16
2: .int 0x00000000,0x3F800000,0x7F800000,0x7FA00000
   .int 0x3E800000,0x3F000000,0x3F400000,0x3FC00000
   .int 0x00000001,0x7FFFFFFF,0x80000000,0xFFFFFFFF
   .int 0xBF800000,0x4F000000,0xCF000001,0x4F800000
   .int 0x80000000,0x4F7FFFFF,0x7F900000,0xFFF00000
   .int 0xCF000000,0x4EFFFFFF,0x7F900000,0xFFF00000

   # vcfux
0: vcfux %v3,%v28,0
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x4F000000,0x4F000000,0x4F800000
0: vcfux %v3,%v28,31
   bl record
   bl check_vector_float_literal
   .int 0x30000000,0x3F800000,0x3F800000,0x40000000

   # vcfsx
0: vcfsx %v3,%v28,0
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x4F000000,0xCF000000,0xBF800000
0: vcfsx %v3,%v28,31
   bl record
   bl check_vector_float_literal
   .int 0x30000000,0x3F800000,0xBF800000,0xB0000000

   # vctuxs
0: vctuxs %v3,%v26,0
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x00000000,0x00000000,0x00000001
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v26
   vctuxs %v3,%v3,0
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x00000000,0x00000000,0x00000001
0: vctuxs %v3,%v29,0
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x80000000,0x00000000,0xFFFFFFFF
0: vctuxs %v3,%v26,31
   bl record
   bl check_vector_int_nosat_literal
   .int 0x20000000,0x40000000,0x60000000,0xC0000000
0: vctuxs %v3,%v30,0
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0xFFFFFF00,0x00000000,0x00000000

   # vctsxs
0: vctsxs %v3,%v26,0
   bl record
   bl check_vector_int_nosat_literal
   .int 0x00000000,0x00000000,0x00000000,0x00000001
0: lvi %v3,1
   mtvscr %v3
   vmr %v3,%v26
   vctsxs %v3,%v3,0
   bl record
   bl check_vector_int_sat_literal
   .int 0x00000000,0x00000000,0x00000000,0x00000001
0: vctsxs %v3,%v29,0
   bl record
   bl check_vector_int_sat_literal
   .int 0xFFFFFFFF,0x7FFFFFFF,0x80000000,0x7FFFFFFF
0: vctsxs %v3,%v26,31
   bl record
   bl check_vector_int_sat_literal
   .int 0x20000000,0x40000000,0x60000000,0x7FFFFFFF
0: vctsxs %v3,%v27,31
   bl record
   bl check_vector_int_sat_literal
   .int 0xE0000000,0xC0000000,0xA0000000,0x80000000
0: vctsxs %v3,%v31,0
   bl record
   bl check_vector_int_nosat_literal
   .int 0x80000000,0x7FFFFF80,0x00000000,0x00000000

   # vrfim
0: vrfim %v3,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
0: vrfim %v3,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0xFF800000,0xFFE00000
0: vrfim %v3,%v26
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x00000000,0x00000000,0x3F800000
0: vrfim %v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0xBF800000,0xBF800000,0xBF800000,0xC0000000

   # vrfin
0: vrfin %v3,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
0: vrfin %v3,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0xFF800000,0xFFE00000
0: vrfin %v3,%v26
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x00000000,0x3F800000,0x40000000
0: vrfin %v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x80000000,0xBF800000,0xC0000000

   # vrfip
0: vrfip %v3,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
0: vrfip %v3,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0xFF800000,0xFFE00000
0: vrfip %v3,%v26
   bl record
   bl check_vector_float_literal
   .int 0x3F800000,0x3F800000,0x3F800000,0x40000000
0: vrfip %v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x80000000,0x80000000,0xBF800000

   # vrfiz
0: vrfiz %v3,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x3F800000,0x7F800000,0x7FE00000
0: vrfiz %v3,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0xBF800000,0xFF800000,0xFFE00000
0: vrfiz %v3,%v26
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x00000000,0x00000000,0x3F800000
0: vrfiz %v3,%v27
   bl record
   bl check_vector_float_literal
   .int 0x80000000,0x80000000,0x80000000,0xBF800000

   ########################################################################
   # Cell-specific instructions: Load/store doubleword with byte reversal
   # (documented in section A.2.1 of "Cell Broadband Engine Programming
   # Handbook, Version 1.1")
   ########################################################################

   # ldbrx
0: addi %r7,%r4,4
   li %r11,-4
   lis %r3,0x0123
   addi %r3,%r3,0x4567
   stw %r3,0(%r4)
   lis %r3,0x89AC
   addi %r3,%r3,0xCDEF-0x10000
   stw %r3,4(%r4)
   ldbrx %r3,%r7,%r11
   bl record
   lis %r11,0xEFCE
   addi %r11,%r11,0xAB89-0x10000
   sldi %r11,%r11,32
   addis %r11,%r11,0x6745
   addi %r11,%r11,0x2301
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r3,0
   li %r0,4
   ldbrx %r3,0,%r4
   bl record
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   # stdbrx
0: li %r11,-4
   lis %r3,0xFEDD
   addi %r3,%r3,0xBA98-0x10000
   sldi %r3,%r3,32
   addis %r3,%r3,0x7654
   addi %r3,%r3,0x3210
   stdbrx %r3,%r7,%r11
   bl record
   ld %r3,0(%r4)
   lis %r11,0x1032
   addi %r11,%r11,0x5477
   sldi %r11,%r11,32
   addis %r11,%r11,0x98BB-0x10000
   addi %r11,%r11,0xDCFE-0x10000
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32
0: li %r0,4
   lis %r3,0xFEDD
   addi %r3,%r3,0xBA98-0x10000
   sldi %r3,%r3,32
   addis %r3,%r3,0x7654
   addi %r3,%r3,0x3210
   stdbrx %r3,0,%r4
   bl record
   lwa %r3,0(%r4)
   lis %r11,0x1032
   addi %r11,%r11,0x5476
   cmpd %r3,%r11
   beq 0f
   std %r3,8(%r6)
   addi %r6,%r6,32

   ########################################################################
   # Cell-specific instructions: Load/store vector left/right (documented
   # in "PowerPC Microprocessor Family: Vector/SIMD Multimedia Extension
   # Technology Programming Environments Manual, Version 2.07c")
   ########################################################################

0: li %r3,256
   li %r0,256
   mtctr %r0
1: stbx %r3,%r4,%r3
   addi %r3,%r3,1
   bdnz 1b
   li %r0,0

   # lvlx/lvlxl
0: li %r3,0x120
   lvlx %v0,%r4,%r3   # Should do the same as lvx.
   bl record
   stv %v0,0,%r4
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r7,0x120(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x128(%r4)
   cmpd %r8,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: li %r3,0x13F
   lvlxl %v1,%r4,%r3  # Should load only one byte.
   bl record
   stv %v1,0,%r4
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   lis %r7,0x3F00
   sldi %r7,%r7,32
   cmpd %r3,%r7
   bne 1f
   cmpdi %r8,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   # lvrx/lvrxl
0: li %r3,0x120
   lvrx %v0,%r4,%r3   # Should load nothing and clear the target register.
   bl record
   stv %v0,0,%r4
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   cmpdi %r3,0
   bne 1f
   cmpdi %r8,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: li %r3,0x13C
   lvrxl %v1,%r4,%r3  # Should load 12 bytes.
   bl record
   stv %v1,0,%r4
   lwz %r3,0(%r4)
   lwz %r8,4(%r4)
   lwz %r9,8(%r4)
   lwz %r10,12(%r4)
   cmpw %r3,%r0
   bne 1f
   lwz %r7,0x130(%r4)
   cmpw %r8,%r7
   bne 1f
   lwz %r7,0x134(%r4)
   cmpw %r9,%r7
   bne 1f
   lwz %r7,0x138(%r4)
   cmpw %r10,%r7
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   # stvlx/stvlxl
0: lv %v0,0x120,%r4
   std %r0,0(%r4)
   std %r0,8(%r4)
   std %r0,16(%r4)
   std %r0,24(%r4)
   stvlx %v0,%r4,%r0  # Should do the same as lvx.
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r9,16(%r4)
   ld %r10,24(%r4)
   ld %r7,0x120(%r4)
   cmpd %r3,%r7
   bne 1f
   ld %r7,0x128(%r4)
   cmpd %r8,%r7
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpdi %r10,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: lv %v1,0x130,%r4
   std %r0,0(%r4)
   std %r0,8(%r4)
   li %r3,0xF
   stvlxl %v1,%r4,%r3  # Should store only one byte.
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r9,16(%r4)
   ld %r10,24(%r4)
   cmpdi %r3,0
   bne 1f
   cmpdi %r8,0x30
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpdi %r10,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   # stvrx/stvrxl
0: lv %v0,0x120,%r4
   std %r0,0(%r4)
   std %r0,8(%r4)
   stvrx %v0,%r4,%r0  # Should store nothing.
   bl record
   ld %r3,0(%r4)
   ld %r8,8(%r4)
   ld %r9,16(%r4)
   ld %r10,24(%r4)
   cmpdi %r3,0
   bne 1f
   cmpdi %r8,0
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpdi %r10,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32
0: lv %v1,0x130,%r4
   std %r0,0(%r4)
   std %r0,8(%r4)
   li %r3,0xC
   stvrxl %v1,%r4,%r3  # Should store 12 bytes.
   bl record
   lwz %r3,0(%r4)
   lwz %r8,4(%r4)
   lwz %r9,8(%r4)
   lwz %r10,12(%r4)
   lwz %r7,0x134(%r4)
   cmpw %r3,%r7
   bne 1f
   lwz %r7,0x138(%r4)
   cmpw %r8,%r7
   bne 1f
   lwz %r7,0x13C(%r4)
   cmpw %r9,%r7
   bne 1f
   cmpw %r10,%r0
   bne 1f
   ld %r7,16(%r4)
   cmpdi %r7,0
   bne 1f
   ld %r7,24(%r4)
   cmpdi %r7,0
   beq 0f
1: std %r3,16(%r6)
   std %r8,24(%r6)
   addi %r6,%r6,32

   ########################################################################
   # Tests for non-Java mode (VSCR[NJ] = 1) with vector instructions.
   # We assume that processing for non-Java mode is shared between all
   # instruction implementations and only test a representative set of
   # operations.
   ########################################################################

0: bl 1f
1: mflr %r31
   addi %r31,%r31,2f-1b
   lv %v24,0,%r31
   lv %v25,16,%r31
   lv %v26,32,%r31
   lv %v27,48,%r31
   lvi %v31,0x10000  # VSCR_NJ
   vspltisb %v0,0
   vspltisb %v1,-1
   lvia %v2,0x80000000
   b 0f
   .balign 16
2: .int 0x00800000,0x00400000,0x80C00000,0x80200000
   .int 0x81000000,0x00800000,0x00800000,0x80000000
   .int 0x00FFFFFE,0x007FFFFF,0x00000000,0x80000000
   .int 0x3F000000,0x40000000,0x00000000,0x00000000

0: vaddfp %v3,%v24,%v25
   bl record
   bl check_vector_float_literal
   .int 0x80800000,0x00C00000,0x80400000,0x80200000
0: mtvscr %v31
   vaddfp %v3,%v25,%v24
   bl record
   bl check_vector_float_literal
   .int 0x80800000,0x00800000,0x80000000,0x80000000
   mtvscr %v0

0: vmaddfp %v3,%v26,%v27,%v0
   bl record
   bl check_vector_float_literal
   .int 0x007FFFFF,0x00FFFFFE,0x00000000,0x00000000
0: vmaddfp %v3,%v26,%v27,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00FFFFFF,0x011FFFFF,0x80C00000,0x80200000
0: mtvscr %v31
   vmaddfp %v3,%v27,%v26,%v0
   bl record
   bl check_vector_float_literal
   .int 0x00000000,0x00000000,0x00000000,0x00000000
   mtvscr %v0
0: mtvscr %v31
   vmaddfp %v3,%v27,%v26,%v24
   bl record
   bl check_vector_float_literal
   .int 0x00FFFFFF,0x00000000,0x80C00000,0x80000000
   mtvscr %v0

   ########################################################################
   # Tests for interference between floating-point and vector rounding modes.
   # Again, we assume the relevant processing is shared and only test a few
   # representative cases.
   ########################################################################

   # Check that setting VSCR[NJ] and executing a vector floating-point
   # instruction does not cause denormals to read as zero in non-vector
   # floating-point instructions.
0: mtfsf 255,%f0    # Clear any junk left over from previous tests.
   mtvscr %v31
   vaddfp %v3,%v0,%v0
   lis %r3,0x0010
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lis %r3,0x0008   # Denormal; should not read as zero.
   sldi %r3,%r3,32
   std %r3,8(%r4)
   lfd %f3,0(%r4)
   lfd %f4,8(%r4)
   fadd %f3,%f3,%f4
   bl record
   lis %r3,0x0018
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %v4,0(%r4)
   bl check_fpu_pnorm
   mtvscr %v0

   # Check that setting VSCR[NJ] does not cause denormals to be flushed to
   # zero in non-vector floating-point instructions.
0: mtvscr %v31
   vaddfp %v3,%v0,%v0
   lis %r3,0x0020
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lis %r3,0x0018
   sldi %r3,%r3,32
   std %r3,8(%r4)
   lfd %f3,0(%r4)
   lfd %f4,8(%r4)
   fsub %f3,%f3,%f4
   bl record
   lis %r3,0x0008
   sldi %r3,%r3,32
   std %r3,0(%r4)
   lfd %v4,0(%r4)
   bl check_fpu_pdenorm
   mtvscr %v0

   # Check that changing the FPSCR rounding mode does not affect vector
   # instructions.
0: mtfsfi 7,3
   lis %r3,0x3F84
   ori %r3,%r3,0x9249
   stw %r3,12(%r4)
   lis %r3,0x3FE0
   stw %r3,28(%r4)
   lfs %f3,12(%r4)
   lfs %f4,28(%r4)
   lv %v3,0,%r4
   lv %v4,16,%r4
   fmuls %f3,%f3,%f4
   vmaddfp %v3,%v3,%v4,%v0
   bl record
   bl check_vector_float_literal
   .int 0,0,0,0x3FE80000  # Should be rounded up (truncated bits are 11).
   mtfsfi 7,0

   # Check that changing the FPSCR rounding mode and executing a vector
   # floating-point instruction does not cause the rounding mode for
   # non-vector instructions to be reset.
0: mtfsfi 7,3
   lis %r3,0x3F84
   ori %r3,%r3,0x9249
   stw %r3,12(%r4)
   lis %r3,0x3FE0
   stw %r3,28(%r4)
   lfs %f4,12(%r4)
   lfs %f5,28(%r4)
   lv %v3,0,%r4
   lv %v4,16,%r4
   fmuls %f3,%f4,%f5
   vmaddfp %v3,%v3,%v4,%v0
   fmuls %f3,%f4,%f5
   bl record
   lis %r3,0x3FE7
   ori %r3,%r3,0xFFFF
   stw %r3,0(%r4)
   lfs %f4,0(%r4)
   bl check_fpu_pnorm_inex
   mtfsfi 7,0

   ########################################################################
   # End of the test code.
   ########################################################################

0: sub %r3,%r6,%r5
   srdi %r3,%r3,5
   lwz %r0,0x7EE4(%r4)
   mtcr %r0
   ld %r0,0x7EE8(%r4)
   mtlr %r0
   ld %r24,0x7EF0(%r4)
   ld %r25,0x7EF8(%r4)
   ld %r26,0x7F00(%r4)
   ld %r27,0x7F08(%r4)
   ld %r28,0x7F10(%r4)
   ld %r29,0x7F18(%r4)
   ld %r30,0x7F20(%r4)
   ld %r31,0x7F28(%r4)
   lfd %f14,0x7F30(%r4)
   lfd %f15,0x7F38(%r4)
   lfd %f24,0x7F40(%r4)
   lfd %f25,0x7F48(%r4)
   lfd %f26,0x7F50(%r4)
   lfd %f27,0x7F58(%r4)
   lfd %f28,0x7F60(%r4)
   lfd %f29,0x7F68(%r4)
   lfd %f30,0x7F70(%r4)
   lfd %f31,0x7F78(%r4)
   lv %v24,0x7F80,%r4
   lv %v25,0x7F90,%r4
   lv %v26,0x7FA0,%r4
   lv %v27,0x7FB0,%r4
   lv %v28,0x7FC0,%r4
   lv %v29,0x7FD0,%r4
   lv %v30,0x7FE0,%r4
   lv %v31,0x7FF0,%r4
   blr

   ########################################################################
   # Subroutines to store an instruction word in the failure buffer.
   # One of these is called for every tested instruction; failures are
   # recorded by advancing the store pointer.
   # On entry:
   #     R6 = pointer at which to store instruction
   # On return:
   #     R8 = destroyed
   #     R9 = destroyed
   ########################################################################

record:
   mflr %r9
   addi %r9,%r9,-8
   lwz %r8,0(%r9)
   stw %r8,0(%r6)
   stw %r9,4(%r6)
   li %r8,0
   std %r8,8(%r6)
   std %r8,16(%r6)
   std %r8,24(%r6)
   blr

   # Alternate version used when the blr is separated by one instruction
   # from the instruction under test.  Used in testing branch instructions.
record2:
   mflr %r9
   addi %r9,%r9,-12
   lwz %r8,0(%r9)
   stw %r8,0(%r6)
   stw %r9,4(%r6)
   li %r8,0
   std %r8,8(%r6)
   std %r8,16(%r6)
   std %r8,24(%r6)
   blr

   ########################################################################
   # Subroutines to validate the result and CR/XER changes from a
   # fixed-point instruction.  On failure, the instruction is automatically
   # recorded in the failure table (assuming a previous "bl record" at the
   # appropriate place).
   # On entry:
   #     R3 = result of instruction
   #     R7 = expected result
   # On return:
   #     R8 = destroyed
   #     R9 = destroyed
   #     XER = 0
   #     CR = 0
   ########################################################################

check_alu:  # CA = 0, OV = 0, SO = 0, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_lt:  # CA = 0, OV = 0, SO = 0, CR0 = less than
   mfcr %r8
   lis %r9,0x4000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_gt:  # CA = 0, OV = 0, SO = 0, CR0 = greater than
   mfcr %r8
   lis %r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_eq:  # CA = 0, OV = 0, SO = 0, CR0 = equal
   mfcr %r8
   lis %r9,0x2000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_undef:  # CA = 0, OV = 0, SO = 0, CR0[0:2] = undefined, CR0[3] = 0
   crclr 0
   crclr 1
   crclr 2
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   cmpdi %r9,0
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ov:  # CA = 0, OV = 1, SO = 1, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   lis %r8,0x6000
   addis %r8,%r8,0x6000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ov_lt:  # CA = 0, OV = 1, SO = 1, CR0 = less than
   mfcr %r8
   lis %r9,0x5000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x6000
   addis %r8,%r8,0x6000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ov_gt:  # CA = 0, OV = 1, SO = 1, CR0 = greater than
   mfcr %r8
   lis %r9,0x5000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x6000
   addis %r8,%r8,0x6000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ov_eq:  # CA = 0, OV = 1, SO = 1, CR0 = equal
   mfcr %r8
   lis %r9,0x3000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x6000
   addis %r8,%r8,0x6000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ov_undef:  # CA = 0, OV = 1, SO = 1, CR0[0:2] = undefined, CR0[3] = 1
   crclr 0
   crclr 1
   crclr 2
   mfcr %r8
   lis %r9,0x1000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x6000
   addis %r8,%r8,0x6000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_so:  # CA = 0, OV = 0, SO = 1, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   lis %r8,0x4000
   addis %r8,%r8,0x4000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_so_lt:  # CA = 0, OV = 0, SO = 1, CR0 = less than
   mfcr %r8
   lis %r9,0x5000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x4000
   addis %r8,%r8,0x4000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_so_gt:  # CA = 0, OV = 0, SO = 1, CR0 = greater than
   mfcr %r8
   lis %r9,0x5000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x4000
   addis %r8,%r8,0x4000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_so_eq:  # CA = 0, OV = 0, SO = 1, CR0 = equal
   mfcr %r8
   lis %r9,0x3000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x4000
   addis %r8,%r8,0x4000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_so_undef:  # CA = 0, OV = 0, SO = 1, CR0[0:2] = undefined, CR0[3] = 1
   crclr 0
   crclr 1
   crclr 2
   mfcr %r8
   lis %r9,0x1000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x4000
   addis %r8,%r8,0x4000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca:  # CA = 1, OV = 0, SO = 0, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   lis %r8,0x2000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_lt:  # CA = 1, OV = 0, SO = 0, CR0 = less than
   mfcr %r8
   lis %r9,0x4000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x2000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_gt:  # CA = 1, OV = 0, SO = 0, CR0 = greater than
   mfcr %r8
   lis %r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x2000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_eq:  # CA = 1, OV = 0, SO = 0, CR0 = equal
   mfcr %r8
   lis %r9,0x2000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   cmpd %r9,%r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_ov:  # CA = 1, OV = 1, SO = 1, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   lis %r8,0x7000
   addis %r8,%r8,0x7000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_ov_lt:  # CA = 1, OV = 1, SO = 1, CR0 = less than
   mfcr %r8
   lis %r9,0x5000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x7000
   addis %r8,%r8,0x7000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_ov_gt:  # CA = 1, OV = 1, SO = 1, CR0 = greater than
   mfcr %r8
   lis %r9,0x5000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x7000
   addis %r8,%r8,0x7000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_ov_eq:  # CA = 1, OV = 1, SO = 1, CR0 = equal
   mfcr %r8
   lis %r9,0x3000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x7000
   addis %r8,%r8,0x7000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_so:  # CA = 1, OV = 0, SO = 1, CR0 not modified
   mfcr %r8
   cmpdi %r8,0
   mfxer %r9
   bne 1f
   lis %r8,0x5000
   addis %r8,%r8,0x5000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_so_lt:  # CA = 1, OV = 0, SO = 1, CR0 = less than
   mfcr %r8
   lis %r9,0x5000
   addis %r9,%r9,0x4000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x5000
   addis %r8,%r8,0x5000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_so_gt:  # CA = 1, OV = 0, SO = 1, CR0 = greater than
   mfcr %r8
   lis %r9,0x5000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x5000
   addis %r8,%r8,0x5000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

check_alu_ca_so_eq:  # CA = 1, OV = 0, SO = 1, CR0 = equal
   mfcr %r8
   lis %r9,0x3000
   cmpd %r8,%r9
   mfxer %r9
   bne 1f
   lis %r8,0x5000
   addis %r8,%r8,0x5000
   cmpd %r9,%r8
   mfcr %r8
   bne 1f
   cmpd %r3,%r7
   beq 0f
1: std %r3,8(%r6)
   std %r8,16(%r6)
   std %r9,24(%r6)
   addi %r6,%r6,32
0: li %r8,0
   mtxer %r8
   mtcr %r8
   blr

   ########################################################################
   # Subroutines to validate the result and CR/FPSCR changes from a
   # floating-point instruction.  On failure, the instruction is
   # automatically recorded in the failure table (assuming a previous
   # "bl record" at the appropriate place).  For "inexact" values (*_inex
   # routines), FX, XX, and FI are automatically added to the set of FPSCR
   # flags in R0.
   # On entry:
   #     F3 = result of instruction
   #     F4 = expected result
   #     R0 = expected value of FPSCR exceptions (from add_fpscr_*)
   #     CR[24:31] = 0
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     R9 = destroyed
   #     FPSCR = all exceptions cleared
   #     CR = 0
   #     0x7000..0x700F(%r4) = destroyed
   ########################################################################

check_fpu_pzero:  # Positive zero, FI = 0
   ori %r0,%r0,0x2000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pzero_inex:  # Positive zero, FI = 1
   oris %r0,%r0,0x8202
   ori %r0,%r0,0x2000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_nzero:  # Negative zero, FI = 0
   oris %r0,%r0,0x0001
   ori %r0,%r0,0x2000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_nzero_inex:  # Negative zero, FI = 1
   oris %r0,%r0,0x8203
   ori %r0,%r0,0x2000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pdenorm:  # Positive denormalized number, FI = 0
   oris %r0,%r0,0x0001
   ori %r0,%r0,0x4000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pdenorm_inex:  # Positive denormalized number, FI = 1
   oris %r0,%r0,0x8203
   ori %r0,%r0,0x4000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_ndenorm:  # Negative denormalized number, FI = 0
   oris %r0,%r0,0x0001
   ori %r0,%r0,0x8000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_ndenorm_inex:  # Negative denormalized number, FI = 1
   oris %r0,%r0,0x8203
   ori %r0,%r0,0x8000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pnorm:  # Positive normalized number, FI = 0
   ori %r0,%r0,0x4000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pnorm_inex:  # Positive normalized number, FI = 1
   oris %r0,%r0,0x8202
   ori %r0,%r0,0x4000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_nnorm:  # Negative normalized number, FI = 0
   ori %r0,%r0,0x8000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_nnorm_inex:  # Negative normalized number, FI = 1
   oris %r0,%r0,0x8202
   ori %r0,%r0,0x8000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pinf:  # Positive infinity, FI = 0
   ori %r0,%r0,0x5000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_pinf_inex:  # Positive infinity, FI = 1
   oris %r0,%r0,0x8202
   ori %r0,%r0,0x5000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_ninf:  # Negative infinity, FI = 0
   ori %r0,%r0,0x9000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_ninf_inex:  # Negative infinity, FI = 1
   oris %r0,%r0,0x8202
   ori %r0,%r0,0x9000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_nan:  # Not a Number, FI = 0
   oris %r0,%r0,0x0001
   ori %r0,%r0,0x1000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   stfd %f3,0x7000(%r4)
   stfd %f4,0x7008(%r4)
   ld %r0,0x7000(%r4)
   ld %r9,0x7008(%r4)
   cmpd %r0,%r9
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_noresult:  # No result (aborted by exception)
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   stfd %f3,0x7000(%r4)
   stfd %f4,0x7008(%r4)
   ld %r0,0x7000(%r4)
   ld %r9,0x7008(%r4)
   cmpd %r0,%r9
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fpu_noresult_nofprf:  # For exception-enabled fctid/fctiw
   mtfsb0 15
   mtfsb0 16
   mtfsb0 17
   mtfsb0 18
   mtfsb0 19
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   stfd %f3,0x7000(%r4)
   stfd %f4,0x7008(%r4)
   ld %r0,0x7000(%r4)
   ld %r9,0x7008(%r4)
   cmpd %r0,%r9
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

   ########################################################################
   # Subroutine to validate the result and CR/FPSCR changes from a
   # floating-point estimation instruction (fres or frsqrte).  Equivalent
   # to check_fpu_pnorm, but allows a range of error for the result and
   # ignores FPSCR[XX] and FPSCR[FI] when checking the state of FPSCR.
   # On entry:
   #     F3 = result of instruction
   #     F4 = lower bound of expected result (inclusive)
   #     F5 = upper bound of expected result (inclusive)
   #     R0 = expected value of FPSCR exceptions (from add_fpscr_*)
   #     CR[24:31] = 0
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     R9 = destroyed
   #     FPSCR = all exceptions cleared
   #     CR = 0
   #     0x7000..0x700F(%r4) = destroyed
   ########################################################################

check_fpu_estimate:
   # XX and FI are undefined for estimation instructions.
   mtfsb0 6
   mtfsb0 14
   ori %r0,%r0,0x4000
   mflr %r9
   bl check_fpscr
   mtlr %r9
   bne 1f
   fcmpu cr0,%f3,%f4
   fcmpu cr1,%f3,%f5
   crnor 2,0,5
   beq 0f
1: stfd %f3,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

   ########################################################################
   # Subroutines to validate the result and CR/FPSCR changes from a
   # floating-point convert-to-integer instruction.  Equivalent to the
   # check_fpu_* routines, except that FPRF is not checked and the
   # expected value is received in an integer register.
   # On entry:
   #     F3 = result of instruction
   #     R7 = expected result
   #     R0 = expected value of FPSCR exceptions (from add_fpscr_*)
   #     CR[24:31] = 0
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     R9 = destroyed
   #     FPSCR = all exceptions and FPRF cleared
   #     CR = 0
   #     0x7000..0x7007(%r4) = destroyed
   ########################################################################

check_fctid:
   mtfsb0 15
   mtfsb0 16
   mtfsb0 17
   mtfsb0 18
   mtfsb0 19
   mflr %r9
   bl check_fpscr
   mtlr %r9
   stfd %f3,0x7000(%r4)
   ld %r9,0x7000(%r4)
   bne 1f
   cmpd %r9,%r7
   beq 0f
1: std %r9,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fctid_inex:
   oris %r0,%r0,0x8202
   mtfsb0 15
   mtfsb0 16
   mtfsb0 17
   mtfsb0 18
   mtfsb0 19
   mflr %r9
   bl check_fpscr
   mtlr %r9
   stfd %f3,0x7000(%r4)
   ld %r9,0x7000(%r4)
   bne 1f
   cmpd %r9,%r7
   beq 0f
1: std %r9,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fctiw:
   mtfsb0 15
   mtfsb0 16
   mtfsb0 17
   mtfsb0 18
   mtfsb0 19
   mflr %r9
   bl check_fpscr
   mtlr %r9
   stfd %f3,0x7000(%r4)
   lwz %r9,0x7004(%r4)
   bne 1f
   cmpw %r9,%r7
   beq 0f
1: std %r9,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_fctiw_inex:
   oris %r0,%r0,0x8202
   mtfsb0 15
   mtfsb0 16
   mtfsb0 17
   mtfsb0 18
   mtfsb0 19
   mflr %r9
   bl check_fpscr
   mtlr %r9
   stfd %f3,0x7000(%r4)
   lwz %r9,0x7004(%r4)
   bne 1f
   cmpw %r9,%r7
   beq 0f
1: std %r9,8(%r6)
   std %r8,16(%r6)
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

   ########################################################################
   # Subroutines to get FPSCR exception flags for use with check_fpu_* and
   # check_fcti*.
   # On entry:
   #     R0 = current set of exception flags
   # On return:
   #     R0 = R0 | requested exception flag
   ########################################################################

add_fpscr_fex:
   oris %r0,%r0,0x4000
   blr

add_fpscr_ox:
   oris %r0,%r0,0x9000
   blr

add_fpscr_ux:
   oris %r0,%r0,0x8800
   blr

add_fpscr_zx:
   oris %r0,%r0,0x8400
   blr

add_fpscr_vxsnan:
   oris %r0,%r0,0xA100
   blr

add_fpscr_vxisi:
   oris %r0,%r0,0xA080
   blr

add_fpscr_vxidi:
   oris %r0,%r0,0xA040
   blr

add_fpscr_vxzdz:
   oris %r0,%r0,0xA020
   blr

add_fpscr_vximz:
   oris %r0,%r0,0xA010
   blr

add_fpscr_vxvc:
   oris %r0,%r0,0xA008
   blr

add_fpscr_vxsqrt:
   oris %r0,%r0,0xA000
   ori %r0,%r0,0x0200
   blr

add_fpscr_vxcvi:
   oris %r0,%r0,0xA000
   ori %r0,%r0,0x0100
   blr

   ########################################################################
   # Subroutine to clear FPSCR[FX] flag for use with check_fpu_* and
   # check_fcti*.
   # On entry:
   #     R0 = current set of exception flags
   # On return:
   #     R0 = R0 & ~0x80000000
   ########################################################################

remove_fpscr_fx:
   oris %r0,%r0,0x8000
   xoris %r0,%r0,0x8000
   blr

   ########################################################################
   # Helper routine for check_fpu_* and check_fcti* to compare FPSCR to an
   # expected value and clear exception flags.
   # On entry:
   #     R0 = expected value of FPSCR (with bits 13 and 24-31 clear)
   # On return:
   #     R8 = FPSCR[0:12] || 0 || FPSCR[14:23] || 0000 0000
   #     FPSCR = all exceptions cleared
   #     CR0 = comparison result
   #     CR[4:23] = destroyed
   ########################################################################

check_fpscr:
   mcrfs cr0,0
   mcrfs cr1,1
   mcrfs cr2,2
   mcrfs cr3,3
   mcrfs cr4,4
   mcrfs cr5,5
   mfcr %r8
   oris %r8,%r8,0x0004
   xoris %r8,%r8,0x0004
   ori %r8,%r8,0x00FF
   xori %r8,%r8,0x00FF
   cmpw %r8,%r0
   blr

   ########################################################################
   # Subroutines to validate the result and VSCR changes from a vector
   # instruction.  On failure, the instruction is automatically recorded in
   # the failure table (assuming a previous "bl record" at the appropriate
   # place).
   # On entry:
   #     V3 = result of instruction
   #     V4 = expected result
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     V4 = destroyed
   #     V5 = destroyed
   #     CR = 0
   #     VSCR[SAT] = 0
   ########################################################################

check_vector_int:  # SAT not modified
check_vector_float:
   vcmpequw. %v4,%v3,%v4
   mfcr %r8
   stw %r8,8(%r6)
   mfvscr %v4
   li %r8,12
   stvewx %v4,%r8,%r6
   bt 24,0f
   stv %v3,16,%r6
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_vector_int_nosat:  # SAT = 0
   vcmpequw. %v4,%v3,%v4
   mfcr %r8
   stw %r8,8(%r6)
   mfvscr %v4
   li %r8,12
   stvewx %v4,%r8,%r6
   vspltisw %v5,1
   vandc %v4,%v4,%v5
   mtvscr %v4
   bf 24,1f
   lwz %r8,12(%r6)
   andi. %r8,%r8,1
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_vector_int_sat:  # SAT = 1
   vcmpequw. %v4,%v3,%v4
   mfcr %r8
   stw %r8,8(%r6)
   mfvscr %v4
   li %r8,12
   stvewx %v4,%r8,%r6
   vspltisw %v5,1
   vandc %v4,%v4,%v5
   mtvscr %v4
   bf 24,1f
   lwz %r8,12(%r6)
   andi. %r8,%r8,1
   bne 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

check_vector_compare_some:  # CR6[0] = 0, CR6[2] = 0
   li %r0,0
   b check_vector_compare_common

check_vector_compare_all:   # CR6[0] = 1, CR6[2] = 0
   li %r0,0x80
   b check_vector_compare_common

check_vector_compare_none:  # CR6[0] = 0, CR6[2] = 1
   li %r0,0x20
   b check_vector_compare_common

check_vector_compare_common:  # Common code for check_vector_compare_*
   mfcr %r8
   stw %r8,8(%r6)
   vcmpequw. %v4,%v3,%v4
   mfvscr %v4
   li %r8,12
   stvewx %v4,%r8,%r6
   bf 24,1f
   lwz %r8,8(%r6)
   cmpw %r8,%r0
   beq 0f
1: stv %v3,16,%r6
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr

   ########################################################################
   # Subroutines to validate the result and VSCR changes from a vector
   # instruction using a literal vector value placed immediately after the
   # instruction.
   # On entry:
   #     V3 = result of instruction
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     V4 = destroyed
   #     V5 = destroyed
   #     V6 = destroyed
   #     CR = 0
   ########################################################################

check_vector_int_literal:
check_vector_float_literal:
   mflr %r8
   lv %v4,0,%r8
   lv %v5,16,%r8
   lvsl %v6,0,%r8
   vperm %v4,%v4,%v5,%v6
   addi %r8,%r8,16
   mtlr %r8
   b check_vector_int

check_vector_int_nosat_literal:
   mflr %r8
   lv %v4,0,%r8
   lv %v5,16,%r8
   lvsl %v6,0,%r8
   vperm %v4,%v4,%v5,%v6
   addi %r8,%r8,16
   mtlr %r8
   b check_vector_int_nosat

check_vector_int_sat_literal:
   mflr %r8
   lv %v4,0,%r8
   lv %v5,16,%r8
   lvsl %v6,0,%r8
   vperm %v4,%v4,%v5,%v6
   addi %r8,%r8,16
   mtlr %r8
   b check_vector_int_sat

   ########################################################################
   # Subroutine to validate the result and VSCR changes from a vector
   # instruction which returns a floating-point estimate.  Note that the
   # bounds should be given in order of magnitude, not value (thus for a
   # range of [-2,-1], put -1 in the first quadword and -2 in the second).
   # On entry:
   #     V3 = result of instruction
   # On return:
   #     R0 = 0
   #     R8 = destroyed
   #     V4 = destroyed
   #     V5 = destroyed
   #     V6 = destroyed
   #     CR = 0
   #     VSCR[SAT] = 0
   ########################################################################

check_vector_float_bounds_literal:
   mflr %r8
   lv %v5,16,%r8
   lv %v4,32,%r8
   lvsl %v6,0,%r8
   vperm %v5,%v5,%v4,%v6
   vcmpgtuw. %v5,%v3,%v5
   mcrf 7,6
   lv %v4,0,%r8
   lv %v5,16,%r8
   addi %r8,%r8,32
   mtlr %r8
   vperm %v4,%v4,%v5,%v6
   vcmpgtuw. %v4,%v4,%v3
   mfcr %r8
   stw %r8,8(%r6)
   mfvscr %v4
   li %r8,12
   stvewx %v4,%r8,%r6
   crand 26,26,30
   bt 26,0f
   stv %v3,16,%r6
   addi %r6,%r6,32
0: li %r0,0
   mtcr %r0
   blr
