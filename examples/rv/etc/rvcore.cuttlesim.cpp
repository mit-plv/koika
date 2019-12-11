#include <iostream>

// #define SIM_FLATTEN
#include "rv32i_core_pipelined.hpp"
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
  virtual bool rule_ExternalI() noexcept {
    {
      bits<1> _c0;
      READ1_FAST(ExternalI, toIMem_valid0, &_c0);
      if (_c0) {
        WRITE1_FAST(ExternalI, toIMem_valid0, 1'0_b);
      } else {
        FAIL(ExternalI);
      }
      struct_mem_req readRequestI;
      READ1_FAST(ExternalI, toIMem_data0, &readRequestI);
      {
        bits<32> IAddress = readRequestI.addr;
        {
          bits<4> IEn = readRequestI.byte_en;
          {
            struct_mem_resp data = struct_mem_resp{};
            data.byte_en = IEn;
            data.addr = IAddress;
            // -- Manually added --
            bits<32> current_value = dmem[IAddress.v >> 2];
            data.data = current_value;
            // --------------------
            bits<1> _x2;
            READ1_FAST(ExternalI, fromIMem_valid0, &_x2);
            if (~(_x2)) {
              WRITE1_FAST(ExternalI, fromIMem_data0, data);
              WRITE1_FAST(ExternalI, fromIMem_valid0, 1'1_b);
            } else {
              FAIL(ExternalI);
            }
          }
        }
      }
    }

    commit_ExternalI();
    return true;
  }

  virtual bool rule_ExternalD() noexcept {
    {
      bits<1> _c0;
      READ1_FAST(ExternalD, toDMem_valid0, &_c0);
      if (_c0) {
        WRITE1_FAST(ExternalD, toDMem_valid0, 1'0_b);
      } else {
        FAIL(ExternalD);
      }
      struct_mem_req readRequestD;
      READ1_FAST(ExternalD, toDMem_data0, &readRequestD);
      {
        bits<32> DAddress = readRequestD.addr;
        {
          bits<4> DEn = readRequestD.byte_en;
          {
            struct_mem_resp data = struct_mem_resp{};
            data.byte_en = DEn;
            data.addr = DAddress;

            // -- Manually added --
            bits<32> current_value = dmem[DAddress.v >> 2];
            if (DAddress.v == 0x40000000 && DEn.v == 0xf) { // PutChar  && DEn.v == 0xf
              putchar((char)readRequestD.data.v);
            } else if (DAddress.v == 0x40001000 && DEn.v == 0xf) {
              std::exit(readRequestD.data.v);
            }
            // else if (DAddress.v == 0xffff4 && DEn.v == 0) { // GetChar
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
            // --------------------

            bits<1> _x2;
            READ1_FAST(ExternalD, fromDMem_valid0, &_x2);
            if (~(_x2)) {
              WRITE1_FAST(ExternalD, fromDMem_data0, data);
              WRITE1_FAST(ExternalD, fromDMem_valid0, 1'1_b);
            } else {
              FAIL(ExternalD);
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
    std::cerr << "Usage: ./rv_core elf_file [ncycles [vcd_path [vcd_period]]]" << std::endl;
    return 1;
  }

  setbuf(stdout, NULL);
  std::ios_base::sync_with_stdio(false);
  cuttlesim::main<rv_core>(argc - 1, argv + 1, argv[1]);
}
#endif

// Local Variables:
// flycheck-clang-include-path: ("../_objects/rv32i_core_pipelined.v/")
// End:
