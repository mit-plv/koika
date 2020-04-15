
// Copyright (c) 2017 Massachusetts Institute of Technology
// 
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#include <iostream>
#include <fstream>
#include <iomanip>

#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "ElfFile.hpp"

void printUsage(const char* program_name) {
    std::cerr << "Usage: " << program_name << " <elf-file> <base-address> <size> <width> <output-hex>" << std::endl;
    std::cerr << "This program converts a specified address range from an ELF file into a hex file" << std::endl;
    std::cerr << "  elf-file        input ELF file to convert to a hex file" << std::endl;
    std::cerr << "  base-address    base address of output hex file" << std::endl;
    std::cerr << "                    This value is interpreted as decimal by default, but it can also be" << std::endl;
    std::cerr << "                    interpreted as octal with a '0' prefix or hex with a '0x' or '0X' prefix" << std::endl;
    std::cerr << "  size            intended size of output hex file in bytes" << std::endl;
    std::cerr << "                    This value can use a K, M, or G suffix" << std::endl;
    std::cerr << "  width           intended width of output hex file in bytes" << std::endl;
    std::cerr << "                    This value must be a power of 2" << std::endl;
    std::cerr << "  output-hex      filename for output hex file" << std::endl;
}

int main(int argc, char* argv[]) {
    if (argc != 6) {
        std::cerr << "ERROR: Incorrect command line arguments" << std::endl;
        printUsage(argv[0]);
        exit(1);
    }

    char *elf_filename = argv[1];
    char *base_address_string = argv[2];
    char *size_string = argv[3];
    char *width_string = argv[4];
    char *hex_filename = argv[5];

    // parse base address
    char *endptr = 0;
    unsigned long long base_address = strtoull(base_address_string, &endptr, 0);
    if (strcmp(endptr, "") != 0) {
        // conversion failure
        std::cerr << "ERROR: base-address expected to be a number" << std::endl;
        printUsage(argv[0]);
        exit(1);
    }

    // parse size
    unsigned long long size = strtoull(size_string, &endptr, 0);
    if (strcmp(endptr, "K") == 0) {
        size *= 1024;
    } else if (strcmp(endptr, "M") == 0) {
        size *= 1024 * 1024;
    } else if (strcmp(endptr, "G") == 0) {
        size *= 1024 * 1024 * 1024;
    } else if (strcmp(endptr, "") != 0) {
        // conversion failure
        std::cerr << "ERROR: size expected to be a number with an optional prefix K, M, or G" << std::endl;
        printUsage(argv[0]);
        exit(1);
    }

    // parse width
    unsigned long long width = strtoull(width_string, &endptr, 0);
    if (strcmp(endptr, "") != 0) {
        // conversion failure
        std::cerr << "ERROR: width expected to be a power of 2" << std::endl;
        printUsage(argv[0]);
        exit(1);
    } else if ((width == 0) || (((width - 1) & width) != 0)) {
        std::cerr << "ERROR: width expected to be a power of 2" << std::endl;
        printUsage(argv[0]);
        exit(1);
    }

    unsigned long logWidth = 0;
    unsigned long long tmpWidth = width >> 1;
    while (tmpWidth != 0) {
        logWidth++;
        tmpWidth = tmpWidth >> 1;
    }

    // Command line arguments are parsed and ready to go

    ElfFile elf_file;
    if (!elf_file.open(elf_filename)) {
        std::cerr << "ERROR: failed opening ELF file" << std::endl;
        exit(1);
    }

    std::vector<ElfFile::Section> sections = elf_file.getSections();

    // write output_buff to hex_filename in hex file format
    std::ofstream hex_file;
    hex_file.open(hex_filename, std::ios_base::out);
    if (!hex_file) {
        std::cerr << "ERROR: unable to open \"" << hex_filename << "\" for writing" << std::endl;
        exit(1);
    }

    uint64_t prev_hex_addr = 0;
    uint64_t curr_hex_addr = 0;
    uint64_t section_offset = 0;
    for (int i = 0 ; i < sections.size() ; i++) {
        if (base_address + size < sections[i].base) {
            // This section starts after the last address in the hex file.
            continue;
        }
        if (sections[i].base < base_address) {
            // This section starts at a lower address than the hex file base
            // address. Compute section_offset to correspond to base_address.
            section_offset = base_address - sections[i].base;
            curr_hex_addr = 0;
        } else {
            curr_hex_addr = sections[i].base - base_address;
            section_offset = 0;
        }

        // assumes 32-bit width for output hex file
        hex_file << "@" << std::hex << std::setw(0) << (curr_hex_addr >> logWidth) << std::endl;
        while ((sections[i].base + section_offset < base_address + size) && (section_offset < sections[i].data_size)) {
            for (int char_index = width-1 ; char_index >= 0 ; char_index--) {
                uint8_t *char_data = (uint8_t*) &sections[i].data[section_offset + char_index];
                hex_file << std::hex << std::setfill('0') << std::setw(2) << (unsigned int) *char_data;
            }
            hex_file << std::endl;
            section_offset += width;
        }
        while ((sections[i].base + section_offset < base_address + size) && (section_offset < sections[i].section_size)) {
            // write zeros
            for (int char_index = width-1 ; char_index >= 0 ; char_index--) {
                hex_file << std::hex << std::setfill('0') << std::setw(2) << 0;
            }
            hex_file << std::endl;
            section_offset += width;
        }
    }

    hex_file << "@" << std::hex << std::setw(0) << (size >> logWidth) << std::endl;

    hex_file.close();

    return 0;
}
