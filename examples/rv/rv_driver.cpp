#include "rv_core.hpp"
#include "elf.h"
#include <iostream>
#include <fstream>
#define IMEM_SIZE 4000000000
#define DMEM_SIZE 4000000000

class extfuns {
public:
  /* External methods (if any) should be implemented here. */
};

using sim_t = module_rv_core<extfuns>;

bits<32>* imem = new bits<32>[IMEM_SIZE];
bits<32>* dmem = new bits<32>[DMEM_SIZE];

class rv_core : public sim_t {

public:
  explicit rv_core(const state_t init) : sim_t(init){}
  void init_imem(char* elf_filename) {
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
	    if ((phdr[i].p_type == PT_LOAD) && (phdr[i].p_memsz > 0)) {
		if (phdr[i].p_memsz < phdr[i].p_filesz) {
		    std::cerr << "ERROR: file size is larger than target memory size" << std::endl;
		    exit(1);
		}
		if ((phdr[i].p_filesz > 0) && (phdr[i].p_offset + phdr[i].p_filesz > elf_size)) {
			std::cerr << "ERROR: file section overflow" << std::endl;
		}
		// Set the corresponding section in IMem
		memcpy(&imem[phdr[i].p_paddr>>2], elf_data + phdr[i].p_offset, phdr[i].p_filesz);
	    }
	}
    } else {
	 std::cerr << "ERROR: the file is not a 32-bit elf file" << std::endl;
	 exit(1);
    }
  }

protected:

   virtual bool rule_externalD() {
    log.fromDMem_valid0.reset(Log.fromDMem_valid0);
    log.fromDMem_data0.reset(Log.fromDMem_data0);
    log.toDMem_data0.reset(Log.toDMem_data0);
    log.toDMem_valid0.reset(Log.toDMem_valid0);

    /* bind */ {
      struct_mem_req readRequestD;
      bits<1> _c0;
      CHECK_RETURN(log.toDMem_valid0.read0(&_c0, state.toDMem_valid0,
					   Log.toDMem_valid0.rwset));
      if (bool(_c0)) {
	CHECK_RETURN(
	    log.toDMem_valid0.write0(UINT8(0x0), Log.toDMem_valid0.rwset));
	CHECK_RETURN(log.toDMem_data0.read0(&readRequestD, state.toDMem_data0,
					    Log.toDMem_data0.rwset));
      } else {
	return false;
      }
      /* bind */ {
	bits<32> DAddress = readRequestD.addr;
	/* bind */ {
	  enum_mem_op DType = readRequestD.type;
	  /* bind */ {
	    struct_mem_resp _x3 =
		prims::unpack<struct_mem_resp, 65>(UINT128(0x000000000));
	    _x3.type = DType;
	    struct_mem_resp _x2 = _x3;
	    _x2.addr = DAddress;
	    struct_mem_resp data = _x2;
	    if (DType == enum_mem_op::Ld) {
	      data.data = dmem[prims::lsr<32,4>(DAddress,2)];
	    } else {
	      dmem[prims::lsr<32,4>(DAddress,2)] = readRequestD.data;
	      data.data = UINT32(0x0000);
	    }
	    bits<1> _x6;
	    CHECK_RETURN(log.fromDMem_valid0.read0(&_x6, state.fromDMem_valid0,
						   Log.fromDMem_valid0.rwset));
	    if (bool(prims::lnot<1>(_x6))) {
	      CHECK_RETURN(
		  log.fromDMem_data0.write0(data, Log.fromDMem_data0.rwset));
	      CHECK_RETURN(log.fromDMem_valid0.write0(
		  UINT8(0x1), Log.fromDMem_valid0.rwset));
	    } else {
	      return false;
	    }
	  }
	}
      }
    }

    Log.fromDMem_valid0 = log.fromDMem_valid0;
    Log.fromDMem_data0 = log.fromDMem_data0;
    Log.toDMem_data0 = log.toDMem_data0;
    Log.toDMem_valid0 = log.toDMem_valid0;
    return true;
  }

  virtual bool rule_externalI() {
    log.fromIMem_data0.reset(Log.fromIMem_data0);
    log.toIMem_data0.reset(Log.toIMem_data0);
    log.fromIMem_valid0.reset(Log.fromIMem_valid0);
    log.toIMem_valid0.reset(Log.toIMem_valid0);

    /* bind */ {
      struct_mem_req readRequestI;
      bits<1> _c0;
      CHECK_RETURN(log.toIMem_valid0.read0(&_c0, state.toIMem_valid0,
					   Log.toIMem_valid0.rwset));
      if (bool(_c0)) {
	CHECK_RETURN(
	    log.toIMem_valid0.write0(UINT8(0x0), Log.toIMem_valid0.rwset));
	CHECK_RETURN(log.toIMem_data0.read0(&readRequestI, state.toIMem_data0,
					    Log.toIMem_data0.rwset));
      } else {
	return false;
      }
      /* bind */ {
	bits<32> IAddress = readRequestI.addr;
	/* bind */ {
	  enum_mem_op IType = readRequestI.type;
	  /* bind */ {
	    struct_mem_resp _x3 =
		prims::unpack<struct_mem_resp, 65>(UINT128(0x000000000));
	    _x3.type = IType;
	    struct_mem_resp _x2 = _x3;
	    _x2.addr = IAddress;
	    struct_mem_resp data = _x2;
	    assert (IType == enum_mem_op::Ld);
	    data.data = imem[prims::lsr<32,4>(IAddress,2)];
	    bits<1> _x6;
	    CHECK_RETURN(log.fromIMem_valid0.read0(&_x6, state.fromIMem_valid0,
						   Log.fromIMem_valid0.rwset));
	    if (bool(prims::lnot<1>(_x6))) {
	      CHECK_RETURN(
		  log.fromIMem_data0.write0(data, Log.fromIMem_data0.rwset));
	      CHECK_RETURN(log.fromIMem_valid0.write0(
		  UINT8(0x1), Log.fromIMem_valid0.rwset));
	    } else {
	      return false;
	    }
	  }
	}
      }
    }

    Log.fromIMem_data0 = log.fromIMem_data0;
    Log.toIMem_data0 = log.toIMem_data0;
    Log.fromIMem_valid0 = log.fromIMem_valid0;
    Log.toIMem_valid0 = log.toIMem_valid0;
    return true;
  }
};


sim_t::state_t init_and_run(char* filename, unsigned long long int ncycles) {
  sim_t::state_t init = {
      .toIMem_data0 =
	  struct_mem_req{enum_mem_op::Ld, UINT32(0x0000), UINT32(0x0000)},
      .toIMem_valid0 = UINT8(0x0),
      .fromIMem_data0 =
	  struct_mem_resp{enum_mem_op::Ld, UINT32(0x0000), UINT32(0x0000)},
      .fromIMem_valid0 = UINT8(0x0),
      .toDMem_data0 =
	  struct_mem_req{enum_mem_op::Ld, UINT32(0x0000), UINT32(0x0000)},
      .toDMem_valid0 = UINT8(0x0),
      .fromDMem_data0 =
	  struct_mem_resp{enum_mem_op::Ld, UINT32(0x0000), UINT32(0x0000)},
      .fromDMem_valid0 = UINT8(0x0),
      .f2d_data0 =
	  struct_fetch_bookkeeping{UINT32(0x0000), UINT32(0x0000), UINT8(0x0)},
      .f2d_valid0 = UINT8(0x0),
      .d2e_data0 =
	  struct_decode_bookkeeping{
	      UINT32(0x0000), UINT32(0x0000), UINT8(0x0),
	      struct_decodedInst{UINT8(0x0), UINT8(0x0), UINT8(0x0), UINT8(0x0),
				 UINT32(0x0000),
				 struct_maybe{UINT8(0x0), enum_immType::ImmI}},
	      UINT32(0x0000), UINT32(0x0000)},
      .d2e_valid0 = UINT8(0x0),
      .e2w_data0 =
	  struct_execute_bookkeeping{
	      UINT32(0x0000),
	      struct_decodedInst{UINT8(0x0), UINT8(0x0), UINT8(0x0), UINT8(0x0),
				 UINT32(0x0000),
				 struct_maybe{UINT8(0x0), enum_immType::ImmI}}},
      .e2w_valid0 = UINT8(0x0),
      .rf_rData_0 = UINT32(0x0000),
      .rf_rData_1 = UINT32(0x0000),
      .rf_rData_2 = UINT32(0x0000),
      .rf_rData_3 = UINT32(0x0000),
      .rf_rData_4 = UINT32(0x0000),
      .rf_rData_5 = UINT32(0x0000),
      .rf_rData_6 = UINT32(0x0000),
      .rf_rData_7 = UINT32(0x0000),
      .rf_rData_8 = UINT32(0x0000),
      .rf_rData_9 = UINT32(0x0000),
      .rf_rData_10 = UINT32(0x0000),
      .rf_rData_11 = UINT32(0x0000),
      .rf_rData_12 = UINT32(0x0000),
      .rf_rData_13 = UINT32(0x0000),
      .rf_rData_14 = UINT32(0x0000),
      .rf_rData_15 = UINT32(0x0000),
      .rf_rData_16 = UINT32(0x0000),
      .rf_rData_17 = UINT32(0x0000),
      .rf_rData_18 = UINT32(0x0000),
      .rf_rData_19 = UINT32(0x0000),
      .rf_rData_20 = UINT32(0x0000),
      .rf_rData_21 = UINT32(0x0000),
      .rf_rData_22 = UINT32(0x0000),
      .rf_rData_23 = UINT32(0x0000),
      .rf_rData_24 = UINT32(0x0000),
      .rf_rData_25 = UINT32(0x0000),
      .rf_rData_26 = UINT32(0x0000),
      .rf_rData_27 = UINT32(0x0000),
      .rf_rData_28 = UINT32(0x0000),
      .rf_rData_29 = UINT32(0x0000),
      .rf_rData_30 = UINT32(0x0000),
      .rf_rData_31 = UINT32(0x0000),
      .scoreboard_rfrData_0 = UINT8(0x0),
      .scoreboard_rfrData_1 = UINT8(0x0),
      .scoreboard_rfrData_2 = UINT8(0x0),
      .scoreboard_rfrData_3 = UINT8(0x0),
      .scoreboard_rfrData_4 = UINT8(0x0),
      .scoreboard_rfrData_5 = UINT8(0x0),
      .scoreboard_rfrData_6 = UINT8(0x0),
      .scoreboard_rfrData_7 = UINT8(0x0),
      .scoreboard_rfrData_8 = UINT8(0x0),
      .scoreboard_rfrData_9 = UINT8(0x0),
      .scoreboard_rfrData_10 = UINT8(0x0),
      .scoreboard_rfrData_11 = UINT8(0x0),
      .scoreboard_rfrData_12 = UINT8(0x0),
      .scoreboard_rfrData_13 = UINT8(0x0),
      .scoreboard_rfrData_14 = UINT8(0x0),
      .scoreboard_rfrData_15 = UINT8(0x0),
      .scoreboard_rfrData_16 = UINT8(0x0),
      .scoreboard_rfrData_17 = UINT8(0x0),
      .scoreboard_rfrData_18 = UINT8(0x0),
      .scoreboard_rfrData_19 = UINT8(0x0),
      .scoreboard_rfrData_20 = UINT8(0x0),
      .scoreboard_rfrData_21 = UINT8(0x0),
      .scoreboard_rfrData_22 = UINT8(0x0),
      .scoreboard_rfrData_23 = UINT8(0x0),
      .scoreboard_rfrData_24 = UINT8(0x0),
      .scoreboard_rfrData_25 = UINT8(0x0),
      .scoreboard_rfrData_26 = UINT8(0x0),
      .scoreboard_rfrData_27 = UINT8(0x0),
      .scoreboard_rfrData_28 = UINT8(0x0),
      .scoreboard_rfrData_29 = UINT8(0x0),
      .scoreboard_rfrData_30 = UINT8(0x0),
      .scoreboard_rfrData_31 = UINT8(0x0),
      .pc = UINT32(0x80000000),
      .epoch = UINT8(0x0),
  };

  rv_core simulator(init);
  simulator.init_imem(filename);
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
