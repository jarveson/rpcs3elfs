This test outputs the stack address of the ppu interrupt thread when it runs, verifying functionality.
It also verifies that the thread is 'stopped' after calling `sys_interrupt_thread_eoi`

hello.spu.self just has three printf's in it, which each generate an interrupt

The ppu interrupt handler thread prints out the current stack address of the interrupt thread, and then handles the actual interrupt (printf) call
The handler thread also has printf's *after* `sys_interrupt_thread_eoi` 
