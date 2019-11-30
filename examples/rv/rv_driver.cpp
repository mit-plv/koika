#include "rv32i_core_pipelined.v.objects/rv32i_core_pipelined.hpp"
#include "elf.h"
#include <iostream>
#include <fstream>
#define DMEM_SIZE 4000000000

class extfuns {
public:
  /* External methods (if any) should be implemented here. */
};

using sim_t = module_rv32i_core_pipelined<extfuns>;

bits<32>* dmem = new bits<32>[DMEM_SIZE];

class rv_core : public sim_t {

public:
  explicit rv_core(const state_t init) : sim_t(init){}
  void init_mem(char* elf_filename) {
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
	    printf("Section of type: %d of size %d filesize %d starting at %x\n", phdr[i].p_type, phdr[i].p_memsz, phdr[i].p_filesz,phdr[i].p_paddr);
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

protected:
  virtual bool rule_ExternalI() {
    reset_ExternalI();

    /* bind */ {
      struct_mem_req readRequestI;
      bits<1> _c0;
      CHECK_RETURN(log.toIMem_valid0.read0(&_c0, Log.toIMem_valid0));
      if (bool(_c0)) {
        CHECK_RETURN(log.toIMem_valid0.write0(1'0_b, Log.toIMem_valid0));
        CHECK_RETURN(log.toIMem_data0.read0(&readRequestI, Log.toIMem_data0));
      } else {
        return false;
      }
      /* bind */ {
        bits<32> IAddress = readRequestI.addr;
        /* bind */ {
          bits<4> IEn = readRequestI.byte_en;
          /* bind */ {
            struct_mem_resp _x3 =
                prims::unpack<struct_mem_resp, 68>(0x68'000000000_x);
            _x3.byte_en = IEn;
            struct_mem_resp _x2 = _x3;
            _x2.addr = IAddress;
            struct_mem_resp data = _x2;
	    // Manually added
	    bits<32> current_value = dmem[IAddress.v >> 2];
	    data.data = current_value;
            bits<1> _x6;
            CHECK_RETURN(log.fromIMem_valid0.read0(&_x6, Log.fromIMem_valid0));
            if (bool(~(_x6))) {
              CHECK_RETURN(
                  log.fromIMem_data0.write0(data, Log.fromIMem_data0));
              CHECK_RETURN(
                  log.fromIMem_valid0.write0(1'1_b, Log.fromIMem_valid0));
            } else {
              return false;
            }
          }
        }
      }
    }

    commit_ExternalI();
    return true;
  }

 virtual bool rule_ExternalD() {
    reset_ExternalD();

    /* bind */ {
      struct_mem_req readRequestD;
      bits<1> _c0;
      CHECK_RETURN(log.toDMem_valid0.read0(&_c0, Log.toDMem_valid0));
      if (bool(_c0)) {
        CHECK_RETURN(log.toDMem_valid0.write0(1'0_b, Log.toDMem_valid0));
        CHECK_RETURN(log.toDMem_data0.read0(&readRequestD, Log.toDMem_data0));
      } else {
        return false;
      }
      /* bind */ {
        bits<32> DAddress = readRequestD.addr;
        /* bind */ {
          bits<4> DEn = readRequestD.byte_en;
          /* bind */ {
            struct_mem_resp _x3 =
                prims::unpack<struct_mem_resp, 68>(0x68'000000000_x);
            _x3.byte_en = DEn;
            struct_mem_resp _x2 = _x3;
            _x2.addr = DAddress;
            struct_mem_resp data = _x2;
	    	    // Manually added
	    bits<32> current_value = dmem[DAddress.v >> 2];
	    if (DAddress.v == 0x40000000 && DEn.v == 0xf) { // PutChar  && DEn.v == 0xf
	      printf("%c", (char) readRequestD.data.v);
	    }
	    if (DAddress.v == 0x40001000 && DEn.v == 0xf) {
	      exit(readRequestD.data.v);
	    }
	   // if (DAddress.v == 0xffff4 && DEn.v == 0) { // GetChar
	   //   scanf("%c", (char *) &data.data.v);
	   // }
	    else {
	      data.data = current_value;
	    }

	    bits<32> mask0 = 0x32'000000ff_x;
	    bits<32> mask1 = 0x32'0000ff00_x;
	    bits<32> mask2 = 0x32'00ff0000_x;
	    bits<32> mask3 = 0x32'ff000000_x;
	    dmem[DAddress.v >> 2] = (DEn[2'0_d].v == 1 ? (readRequestD.data & mask0) : (current_value & mask0))
	      | (DEn[2'1_d].v == 1 ? (readRequestD.data & mask1) : (current_value & mask1))
	      | (DEn[2'2_d].v == 1 ? (readRequestD.data & mask2) : (current_value & mask2))
	      | (DEn[2'3_d].v == 1 ? (readRequestD.data & mask3) : (current_value & mask3));
            bits<1> _x6;
            CHECK_RETURN(log.fromDMem_valid0.read0(&_x6, Log.fromDMem_valid0));
            if (bool(~(_x6))) {
              CHECK_RETURN(
                  log.fromDMem_data0.write0(data, Log.fromDMem_data0));
              CHECK_RETURN(
                  log.fromDMem_valid0.write0(1'1_b, Log.fromDMem_valid0));
            } else {
              return false;
            }
          }
        }
      }
    }

    commit_ExternalD();
    return true;
  }

};


sim_t::state_t init_and_run(char* filename, unsigned long long int ncycles) {
  sim_t::state_t init = {
      .toIMem_data0 = struct_mem_req{4'0000_b, 32'0_b, 32'0_b},
      .toIMem_valid0 = 1'0_b,
      .fromIMem_data0 = struct_mem_resp{4'0000_b, 32'0_b, 32'0_b},
      .fromIMem_valid0 = 1'0_b,
      .toDMem_data0 = struct_mem_req{4'0000_b, 32'0_b, 32'0_b},
      .toDMem_valid0 = 1'0_b,
      .fromDMem_data0 = struct_mem_resp{4'0000_b, 32'0_b, 32'0_b},
      .fromDMem_valid0 = 1'0_b,
      .f2d_data0 = struct_fetch_bookkeeping{32'0_b, 32'0_b, 1'0_b},
      .f2d_valid0 = 1'0_b,
      .f2dprim_data0 = struct_fetch_bookkeeping{32'0_b, 32'0_b, 1'0_b},
      .f2dprim_valid0 = 1'0_b,
      .d2e_data0 =
          struct_decode_bookkeeping{
              32'0_b, 32'0_b, 1'0_b,
              struct_decodedInst{1'0_b, 1'0_b, 1'0_b, 1'0_b, 32'0_b,
                                 struct_maybe{1'0_b, enum_immType::ImmI}},
              32'0_b, 32'0_b},
      .d2e_valid0 = 1'0_b,
      .e2w_data0 =
          struct_execute_bookkeeping{
              1'0_b, 2'00_b, 2'00_b, 32'0_b,
              struct_decodedInst{1'0_b, 1'0_b, 1'0_b, 1'0_b, 32'0_b,
                                 struct_maybe{1'0_b, enum_immType::ImmI}}},
      .e2w_valid0 = 1'0_b,
      .rf_rData_0 = 32'0_b,
      .rf_rData_1 = 32'0_b,
      .rf_rData_2 = 32'0_b,
      .rf_rData_3 = 32'0_b,
      .rf_rData_4 = 32'0_b,
      .rf_rData_5 = 32'0_b,
      .rf_rData_6 = 32'0_b,
      .rf_rData_7 = 32'0_b,
      .rf_rData_8 = 32'0_b,
      .rf_rData_9 = 32'0_b,
      .rf_rData_10 = 32'0_b,
      .rf_rData_11 = 32'0_b,
      .rf_rData_12 = 32'0_b,
      .rf_rData_13 = 32'0_b,
      .rf_rData_14 = 32'0_b,
      .rf_rData_15 = 32'0_b,
      .rf_rData_16 = 32'0_b,
      .rf_rData_17 = 32'0_b,
      .rf_rData_18 = 32'0_b,
      .rf_rData_19 = 32'0_b,
      .rf_rData_20 = 32'0_b,
      .rf_rData_21 = 32'0_b,
      .rf_rData_22 = 32'0_b,
      .rf_rData_23 = 32'0_b,
      .rf_rData_24 = 32'0_b,
      .rf_rData_25 = 32'0_b,
      .rf_rData_26 = 32'0_b,
      .rf_rData_27 = 32'0_b,
      .rf_rData_28 = 32'0_b,
      .rf_rData_29 = 32'0_b,
      .rf_rData_30 = 32'0_b,
      .rf_rData_31 = 32'0_b,
      .scoreboard_Scores_rData_0 = 2'00_b,
      .scoreboard_Scores_rData_1 = 2'00_b,
      .scoreboard_Scores_rData_2 = 2'00_b,
      .scoreboard_Scores_rData_3 = 2'00_b,
      .scoreboard_Scores_rData_4 = 2'00_b,
      .scoreboard_Scores_rData_5 = 2'00_b,
      .scoreboard_Scores_rData_6 = 2'00_b,
      .scoreboard_Scores_rData_7 = 2'00_b,
      .scoreboard_Scores_rData_8 = 2'00_b,
      .scoreboard_Scores_rData_9 = 2'00_b,
      .scoreboard_Scores_rData_10 = 2'00_b,
      .scoreboard_Scores_rData_11 = 2'00_b,
      .scoreboard_Scores_rData_12 = 2'00_b,
      .scoreboard_Scores_rData_13 = 2'00_b,
      .scoreboard_Scores_rData_14 = 2'00_b,
      .scoreboard_Scores_rData_15 = 2'00_b,
      .scoreboard_Scores_rData_16 = 2'00_b,
      .scoreboard_Scores_rData_17 = 2'00_b,
      .scoreboard_Scores_rData_18 = 2'00_b,
      .scoreboard_Scores_rData_19 = 2'00_b,
      .scoreboard_Scores_rData_20 = 2'00_b,
      .scoreboard_Scores_rData_21 = 2'00_b,
      .scoreboard_Scores_rData_22 = 2'00_b,
      .scoreboard_Scores_rData_23 = 2'00_b,
      .scoreboard_Scores_rData_24 = 2'00_b,
      .scoreboard_Scores_rData_25 = 2'00_b,
      .scoreboard_Scores_rData_26 = 2'00_b,
      .scoreboard_Scores_rData_27 = 2'00_b,
      .scoreboard_Scores_rData_28 = 2'00_b,
      .scoreboard_Scores_rData_29 = 2'00_b,
      .scoreboard_Scores_rData_30 = 2'00_b,
      .scoreboard_Scores_rData_31 = 2'00_b,
      .inst_count = 32'0_b,
      .pc = 32'0_b,
      .epoch = 1'0_b,
  };

  rv_core simulator(init);
  simulator.init_mem(filename);
  simulator.run(ncycles);
  return simulator.snapshot();
}


#ifndef SIM_MINIMAL
int main(int argc, char **argv) {
  unsigned long long int ncycles = 1000;
  char* filename;
  if (argc >= 3) {
    ncycles = std::stoull(argv[2]);
    filename = argv[1];
  } else {
	std::cerr << "Argument missing.\n\nUsage: ./rv_core elf_file number_cycles" << std::endl;
	exit(1);
  }

  sim_t::state_t snapshot = init_and_run(filename,ncycles);
  snapshot.dump();
  return 0;
}
#endif
