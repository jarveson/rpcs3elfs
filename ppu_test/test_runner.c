
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#define __CELL_ASSERT__ 
#include <assert.h>

extern int test(int zero, void *scratch, void *failures, double one);

int main(void)
{   
    char *scratchBuf = malloc(32768);
    char *failedBuf = malloc(65536);

    printf("Starting / Running tests\n");

    int ret = test(0, scratchBuf, failedBuf, (double)1.0);

    if (ret == 0) {
        printf("No failures detected!\n");
    }
    else if (ret < 0) {
        printf("Code failed to bootstrap itself\n");
    }
    else {
        // excerpt from cell-ppu.s , see file for more info
        /*# On return, if R3 > 0 then the buffer in R5 contains R3 failure records.
        # Each failure record is 8 words (32 bytes) long and has the following
        # format:
        #    Word 0: Failing instruction word
        #    Word 1: Address of failing instruction word
        #    Words 2-7: Auxiliary data (see below)
        # Instructions have been coded so that generally, the operands uniquely
        # identify the failing instruction, but in some cases (such as rounding
        # mode tests with frsp) there are multiple copies of the same instruction
        # in different locations; in such cases, use the address to locate the
        # failing instruction.*/
        printf("%d failed instructions\n", ret);
        uint32_t *fail = (uint32_t*)failedBuf;
        for (int i=0; i < ret; ++i) {
            printf("-------------------------------------------\n");
            printf("Failed inst: 0x%x, addr 0x%x\n", fail[0], fail[1]);
            printf("Aux Data: 0x%x 0x%x\n", fail[2], fail[3]);
            printf("0x%x 0x%x 0x%x 0x%x\n", fail[4], fail[5], fail[6], fail[7]);
            fail += 8;
        }

        printf("Throwing assert\n");
        assert(0);
    }
    free(scratchBuf);
    free(failedBuf);
    return 0;
}
