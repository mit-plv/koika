
// Copyright (c) 2017 Massachusetts Institute of Technology

// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#include <fstream>
#include <iostream>

#if defined(__APPLE__)
#include "elf.h"
#else
#include <elf.h>
#endif

#include "ElfFile.hpp"

ElfFile::ElfFile() {
    elf_size = 0;
    elf_data = nullptr;
    elf_bit_width = 0;
}

bool ElfFile::open(char* filename) {
    // load filename into elf_data and set elf_size
    std::ifstream elf_file;
    elf_file.open(filename, std::ios::in | std::ios::binary);

    if (!elf_file.is_open()) {
        std::cerr << "ERROR: ElfFile::open(): failed opening file \"" << filename << "\"" << std::endl;
        return false;
    }

    elf_file.seekg(0, elf_file.end);
    elf_size = elf_file.tellg();
    elf_file.seekg(0, elf_file.beg);

    elf_data = new char[elf_size];
    elf_file.read(elf_data, elf_size);

    if (!elf_file) {
        std::cerr << "ERROR: ElfFile::open(): failed reading elf file" << std::endl;
        elf_size = 0;
        delete[] elf_data;
        elf_data = nullptr;
        return false;
    }

    if (elf_size < sizeof(Elf32_Ehdr)) {
        std::cerr << "ERROR: ElfFile::open(): file too small to be a valid elf file" << std::endl;
        elf_size = 0;
        delete[] elf_data;
        elf_data = nullptr;
        return false;
    }

    // make sure the header matches elf32 or elf64
    Elf32_Ehdr *ehdr = (Elf32_Ehdr *) elf_data;
    unsigned char* e_ident = ehdr->e_ident;
    if (e_ident[EI_MAG0] != ELFMAG0
            || e_ident[EI_MAG1] != ELFMAG1
            || e_ident[EI_MAG2] != ELFMAG2
            || e_ident[EI_MAG3] != ELFMAG3) {
        std::cerr << "ERROR: ElfFile::open(): file is not an elf file" << std::endl;
        elf_size = 0;
        delete[] elf_data;
        elf_data = nullptr;
        return false;
    }

    bool success = false;
    if (e_ident[EI_CLASS] == ELFCLASS32) {
        // 32-bit ELF
        elf_bit_width = 32;
        success = finishLoad<Elf32_Ehdr, Elf32_Phdr>();
    } else if (e_ident[EI_CLASS] == ELFCLASS64) {
        // 64-bit ELF
        elf_bit_width = 64;
        success = finishLoad<Elf64_Ehdr, Elf64_Phdr>();
    } else {
        std::cerr << "ERROR: ElfFile::open(): file is neither 32-bit nor 64-bit" << std::endl;
        elf_size = 0;
        delete[] elf_data;
        elf_data = nullptr;
        return false;
    }

    if (success) {
        return true;
    } else {
        std::cerr << "ERROR: ElfFile::open(): finishLoad() failed" << std::endl;
        elf_size = 0;
        delete[] elf_data;
        elf_data = nullptr;
        return false;
    }
}

const std::vector<ElfFile::Section>& ElfFile::getSections() {
    return sections;
}

template <typename Elf_Ehdr, typename Elf_Phdr>
bool ElfFile::finishLoad() {
    // This uses templated types to support 32-bit and 64-bit elfs
    Elf_Ehdr *ehdr = (Elf_Ehdr*) elf_data;
    Elf_Phdr *phdr = (Elf_Phdr*) (elf_data + ehdr->e_phoff);
    if (elf_size < ehdr->e_phoff + ehdr->e_phnum * sizeof(Elf_Phdr)) {
        std::cerr << "ERROR: ElfFile::finishLoad(): file too small for expected number of program header tables" << std::endl;
        return false;
    }
    // loop through program header tables
    for (int i = 0 ; i < ehdr->e_phnum ; i++) {
        // only look at non-zero length PT_LOAD sections
        if ((phdr[i].p_type == PT_LOAD) && (phdr[i].p_memsz > 0)) {
            if (phdr[i].p_memsz < phdr[i].p_filesz) {
                std::cerr << "ERROR: ElfFile::finishLoad(): file size is larger than memory size" << std::endl;
                return false;
            }
            if (phdr[i].p_filesz > 0) {
                if (phdr[i].p_offset + phdr[i].p_filesz > elf_size) {
                    std::cerr << "ERROR: ElfFile::finishLoad(): file section overflow" << std::endl;
                    return false;
                }
            }
            Section curr_section;
            curr_section.base = phdr[i].p_paddr; // maybe p_vaddr?
            curr_section.section_size = phdr[i].p_memsz;
            curr_section.data_size = phdr[i].p_filesz;
            curr_section.data = elf_data + phdr[i].p_offset;
            sections.push_back(curr_section);
        }
    }
    return true;
}

