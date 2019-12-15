/*! C++ driver for rv32i simulation with Cuttlesim !*/
#include <iostream>
#include <optional>

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

#define PEEK(rn) log.state.rn

  virtual bool rule_ExternalI() noexcept {
    static std::optional<struct_mem_req> last{};

    if (~PEEK(fromIMem_valid0) && last.has_value()) {
      PEEK(fromIMem_valid0) = 1'1_b;
      PEEK(fromIMem_data0) = struct_mem_resp {
        .byte_en = last->byte_en,
        .addr = last->addr,
        .data = dmem[last->addr.v >> 2]
      };
      last.reset();
    }

    if (PEEK(toIMem_valid0) && !last.has_value()) {
      PEEK(toIMem_valid0) = 1'0_b;
      last = PEEK(toIMem_data0);
    }

    COMMIT(ExternalI);
    return true;
  }

  virtual bool rule_ExternalD() noexcept {
    static std::optional<struct_mem_req> last{};

    if (!PEEK(fromDMem_valid0) && last.has_value()) {
      PEEK(fromDMem_valid0) = 1'1_b;

      auto data = last->data;
      auto addr = last->addr;
      auto dEn = last->byte_en;
      auto current = dmem[addr.v >> 2];

      PEEK(fromDMem_data0) = struct_mem_resp {
        .byte_en = last->byte_en,
        .addr = last->addr,
        .data = current
      };

      if (addr.v == 0x40000000 && dEn.v == 0xf) { // PutChar
        putchar(static_cast<char>(last->data.v));
      } else if (addr.v == 0x40001000 && dEn.v == 0xf) {
        std::exit(last->data.v);
      } // else if (addr == 0xffff4 && dEn.v == 0) { // GetChar
      //   data.data.v = getchar();
      // }
      else {
        dmem[addr.v >> 2] =
          ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
          ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
          ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
          ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);
      }

      last.reset();
    }

    if (PEEK(toDMem_valid0) && !last.has_value()) {
      PEEK(toDMem_valid0) = 1'0_b;
      last = PEEK(toDMem_data0);
    }

    COMMIT(ExternalD);
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
// flycheck-clang-language-standard: "c++17"
// End:
