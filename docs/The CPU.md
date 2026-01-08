# The CPU

The nes has the 2A03 based on the 6502 chip.

## Features

* 16 bit for memory addressing.
* access to RAM via 0x0000 to 0x2000 address space (excluding the last, so the biggest address to access RAM would be 0x1FFF).
* 6 registers.

## Registers

The CPU has the following registers:

* The Program Counter: while all the below registers are 8 bit, this one is 16 bit, the address of the next instruction to be executed.
* The Stack Pointer: memory space from 0x0100 to 0x01FF used for the stack. It holds the address of the top that space.
  The stack grows from top to bottom (as all stacks. 0x01FF to 0x0100). So when we insert a value to the stack the SP decrements,
  and when we pop a value from the stack the SP increments.
* The Accumulator: stores the results of arithmetic, logic, and memory access operations. It used as an input parameter for some operations.
* The Index X: used as an offset in specific memory addressing modes. Can be used for auxiliary storage needs.
* The Index Y: same as X.
* The Processor Status: this one is only 8 bit, where each bit is used as a flag to represent a 
  state. Although we have 8 bit, only 7 of this bits are used while the other one is discarded. This flags can be set or unset depending on
  the result of the last executed instruction.


## How to write to RAM?

We have 2KiB of RAM, although we can access to RAM reading/writing to 0x0000 to 0x1FFF, the RAM can only accept addresses from
0x0000 to 0x07FF, so anything higher than that would result in a "Mirror" or "Saturation", e.g the cpu writes to 0x08FF, RAM will
"apply" a mask (0x07FF) that way it accepts valid addresses, anything higher than 0x07FF will result in reading the same memory cell.
0x08FF, 0x09FF, etc, will write in 0x07FF.
