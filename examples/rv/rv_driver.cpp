#include <iostream>

#include "rv32i_core_pipelined.v.objects/rv32i_core_pipelined.hpp"
#include "elf.hpp"

#define DMEM_SIZE (static_cast<std::size_t>(1) << 30)

using simulator = module_rv32i_core_pipelined<unit>;

class rv_core : public simulator {
  std::unique_ptr<bits<32>[]> dmem;

public:
  explicit rv_core(const std::string& elf_fpath)
    // Use new … instead of make_unique to avoid 0-initialization
    : simulator{}, dmem(new bits<32>[DMEM_SIZE]) {
    elf_load(reinterpret_cast<uint32_t*>(dmem.get()), elf_fpath.c_str());
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
              putchar((char)readRequestD.data.v);
            }
            if (DAddress.v == 0x40001000 && DEn.v == 0xf) {
              exit(readRequestD.data.v);
            }
            // if (DAddress.v == 0xffff4 && DEn.v == 0) { // GetChar
            //   data.data.v = getchar();
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

#ifdef SIM_MINIMAL
template simulator::state_t cuttlesim::init_and_run<simulator>(int);
#else
int main(int argc, char** argv) {
  if (argc <= 1) {
    std::cerr << "Usage: ./rv_core elf_file [number_cycles [vcd_path [vcd_period]]]" << std::endl;
    return 1;
  }

  setbuf(stdout, NULL);
  std::ios_base::sync_with_stdio(false);
  cuttlesim::main<rv_core>(argc - 1, argv + 1, argv[1]);
}
#endif
