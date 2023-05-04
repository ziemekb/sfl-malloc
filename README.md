# Segregated free list malloc
Project carried out in Operating Systems course. Our task was to implement dynamic memory allocator for C programs. Our implementation had to balance good throughput with efficient use of space.

## Overview
mm.c file provides my implementation of ```malloc()```, ```realloc()```, ```calloc()``` and ```free()``` functions. 
My implementation uses segregated free list technique, precisely free blocks of size from 16 to 256 are put into their own lists and larger blocks are put into lists with size classes. 

```
Allocated block structure:

 |==================|
 |        |         |
 | HEADER | PAYLOAD |
 |        |         |
 |==================|
```

```
Free block structure:

 |============================================|
 |        | NEXT  | PREVIOUS |       |        |
 | HEADER | FREE  | FREE     |  ...  | FOOTER |
 |        | BLOCK | BLOCK    |       |        |
 |============================================|
```

Headers store information about size and allocation of the block and whether the previous block is free.
Footers are identical copies of headers.
Headers and footers are unsigned integers and take 4 bytes.

Allocated blocks have only headers and of course payload.
Free blocks have headers, footers and store information about the next and previous free blocks in the list.
The next free block and previous free block fields are signed integers and indicate the distance between next and previous block in the list, with one unit being equal ALIGNMENT.
Thanks to this compression minimal block size is 16 bytes.

## Usage
To test the allocator do the following:

Clone the repo on your local machine:
  ```
  git clone https://github.com/ziemekb/sfl-malloc.git
  ```
And cd into the folder and execute make:
  ```
  cd sfl-malloc
  make
  ```
Now you can test the allocator on files provided in catalog traces via ```./mdriver``` command.
To check the usage type ```./mdriver -h```.
