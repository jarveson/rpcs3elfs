#include <stdio.h>
#include <stdlib.h>

#include <sys/types.h>
#include <sys/process.h>

#include <sys/ppu_thread.h>
#include <sys/memory.h>

// Set priority and stack size for the primary PPU thread.
// Priority : 1000
// Stack    : 64KB
SYS_PROCESS_PARAM(1000, 0x10000)

sys_memory_t memory_id;
sys_addr_t addr1;
sys_addr_t addr2;
sys_event_queue_t queue_id;


int main() {

    printf("sys_memory test start.\n");

	sys_memory_info_t userMem;
	int ret = sys_memory_get_user_memory_size( &userMem );
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_get_user_memory_size\n", ret);
		return(CELL_OK);
	}
	
	printf("sys_memory_get_user_memory_size:\n");
	printf("userMem total: 0x%x\n", userMem.total_user_memory);
	printf("userMem avail: 0x%x\n", userMem.available_user_memory);
	
	uint32_t addr;
	ret = sys_memory_allocate(0x10000, 0x200, &addr);
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_allocate\n", ret);
		return(CELL_OK);
	}
	
	printf("allocated 0x10000 at 0x%x\n", addr);
	
	ret = sys_memory_get_user_memory_size( &userMem );
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_get_user_memory_size\n", ret);
		return(CELL_OK);
	}
	
	printf("sys_memory_get_user_memory_size:\n");
	printf("userMem total: 0x%x\n", userMem.total_user_memory);
	printf("userMem avail: 0x%x\n", userMem.available_user_memory);
	
	ret = sys_memory_free(addr);
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_free\n", ret);
		return(CELL_OK);
	}
	
	sys_memory_container_t cid;
	ret = sys_memory_container_create(&cid, userMem.available_user_memory);
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_container_create\n", ret);
		return(CELL_OK);
	}
	
	printf("allocated full size\n");
	
	ret = sys_memory_get_user_memory_size( &userMem );
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_get_user_memory_size\n", ret);
		return(CELL_OK);
	}
	printf("sys_memory_get_user_memory_size:\n");
	printf("userMem total: 0x%x\n", userMem.total_user_memory);
	printf("userMem avail: 0x%x\n", userMem.available_user_memory);
	
	
	ret = sys_memory_container_get_size(&userMem, cid);
	if (ret != 0) {
		printf ("Error(%08X) : sys_memory_container_get_size\n", ret);
		return(CELL_OK);
	}
	printf("sys_memory_container_get_size:\n");
	printf("userMem total: 0x%x\n", userMem.total_user_memory);
	printf("userMem avail: 0x%x\n", userMem.available_user_memory);
	
    printf("sample finished.\n");

    return 0;
}