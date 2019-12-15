/*! Support for loading ELF files !*/

// Copyright 2016-2019 Massachusetts Institute of Technology
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
// IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

#include <elf.h>
#include <cstring>
#include <fstream>
#include <iostream>

void __attribute__((noinline)) elf_load(uint32_t* dmem, const char* elf_filename) {
  std::ifstream elf_file;
  char* elf_data;
  unsigned long long elf_size;

  elf_file.open(elf_filename, std::ios::in | std::ios::binary);

  if (!elf_file) {
	std::cerr << "ERROR: fail reading elf file" << std::endl;
	exit(1);
  }

  // Get size of the elf
  elf_file.seekg(0, elf_file.end);
  elf_size = elf_file.tellg();
  elf_file.seekg(0, elf_file.beg);

  if (!elf_file) {
	std::cerr << "ERROR: fail reading elf file" << std::endl;
	exit(1);
  }

  if (elf_size < sizeof(Elf32_Ehdr)) {
	std::cerr << "ERROR: the file is too small to be a valid elf" << std::endl;
	exit(1);
  }

  elf_data = new char[elf_size];
  elf_file.read(elf_data, elf_size);

  // Check header
  Elf32_Ehdr *ehdr = (Elf32_Ehdr *) elf_data;
  unsigned char* e_ident = ehdr->e_ident;
  if (e_ident[EI_MAG0] != ELFMAG0
      || e_ident[EI_MAG1] != ELFMAG1
      || e_ident[EI_MAG2] != ELFMAG2
      || e_ident[EI_MAG3] != ELFMAG3) {
	std::cerr << "ERROR: the file is not a valid elf file" << std::endl;
	exit(1);
  }

  if (e_ident[EI_CLASS] == ELFCLASS32) {
	// 32-bit ELF, only case supported
	Elf32_Ehdr *ehdr = (Elf32_Ehdr*) elf_data;
	Elf32_Phdr *phdr = (Elf32_Phdr*) (elf_data + ehdr->e_phoff);
	if (elf_size < ehdr->e_phoff + ehdr->e_phnum * sizeof(Elf32_Phdr)) {
      std::cerr << "ERROR: file too small for expected number of program header tables" << std::endl;
      exit(1);
	}
	// loop through program header tables
	for (int i = 0 ; i < ehdr->e_phnum ; i++) {
      // only look at non-zero length PT_LOAD sections
      // printf("Section of type: %d of size %d filesize %d starting at %x\n", phdr[i].p_type, phdr[i].p_memsz, phdr[i].p_filesz,phdr[i].p_paddr);
      if ((phdr[i].p_type == PT_LOAD) && (phdr[i].p_memsz > 0)) {
		if (phdr[i].p_memsz < phdr[i].p_filesz) {
          std::cerr << "ERROR: file size is larger than target memory size" << std::endl;
          exit(1);
		}
		if ((phdr[i].p_filesz > 0) && (phdr[i].p_offset + phdr[i].p_filesz > elf_size)) {
          std::cerr << "ERROR: file section overflow" << std::endl;
		}
		// Set the corresponding section in IMem
		memcpy(&dmem[phdr[i].p_paddr>>2], elf_data + phdr[i].p_offset, phdr[i].p_filesz);
      }
	}
  } else {
    std::cerr << "ERROR: the file is not a 32-bit elf file" << std::endl;
    exit(1);
  }
}
