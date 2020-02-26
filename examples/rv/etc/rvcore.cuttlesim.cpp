/*! C++ driver for rv32i simulation with Cuttlesim !*/
#include <iostream>
#include <optional>

#include "rv32.hpp"
#include "elf.hpp"
#include "cuttlesim.hpp"

#define DMEM_SIZE (static_cast<std::size_t>(1) << 25)

struct bram {
  std::unique_ptr<bits<32>[]> mem;
  std::optional<struct_mem_req> last;

  struct_maybe_mem_resp get(struct_maybe_bits_0 opt_req) {
    if (!opt_req.valid || !last.has_value())
      return struct_maybe_mem_resp { .valid = {0}, .data = struct_mem_resp{} };

    auto data = last->data;
    auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> current = bits<32>{0};

    if (addr.v == 0x40000000 && dEn.v == 0xf) { // PutChar
      putchar(static_cast<char>(last->data.v));
    } else if (addr.v == 0x40001000 && dEn.v == 0xf) {
      int exitcode = last->data.v;
      if (exitcode == 0) {
        printf("  [0;32mPASS[0m\n");
      } else {
        printf("  [0;31mFAIL[0m (%d)", exitcode);
      }
      std::exit(exitcode);
    } else {
      current = mem[addr.v >> 2];
      mem[addr.v >> 2] =
        ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
        ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
        ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
        ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);
    }

    last.reset();
    return {
      .valid = {1},
      .data = { .byte_en = dEn, .addr = addr, .data = current }
    };
  }

  struct_maybe_bits_0 put(struct_maybe_mem_req opt_req) {
    if (!opt_req.valid || last.has_value())
      return struct_maybe_bits_0{ .valid = {0}, .data = prims::tt };

    last = opt_req.data;
    return { .valid = {1}, .data = prims::tt };
  }

  void read_elf(const std::string& elf_fpath) {
    elf_load(reinterpret_cast<uint32_t*>(mem.get()), elf_fpath.c_str());
  }

  // Use new … instead of make_unique to avoid 0-initialization
  bram() : mem{new bits<32>[DMEM_SIZE]}, last{} {}
};

struct extfuns_t {
  bram dmem, imem;

  struct_maybe_mem_resp ext_mem_dmem_mget(struct_maybe_bits_0 req) {
    return dmem.get(req);
  }
#undef RULE_NAME

  struct_maybe_mem_resp ext_mem_imem_mget(struct_maybe_bits_0 req) {
    return imem.get(req);
  }

  struct_maybe_bits_0 ext_mem_dmem_mput(struct_maybe_mem_req req) {
    return dmem.put(req);
  }

  struct_maybe_bits_0 ext_mem_imem_mput(struct_maybe_mem_req req) {
    return imem.put(req);
  }

  extfuns_t() : dmem{}, imem{} {}
};

using simulator = module_rv32<extfuns_t>;

class rv_core : public simulator {
  void strobe(std::uint_fast64_t ncycles) const {
#if defined(SIM_STROBE) && !defined(SIM_MINIMAL)
    std::cout << "# " << ncycles << std::endl;
    std::cout << "pc = " << Log.state.pc << std::endl;
    std::cout << "epoch = " << Log.state.epoch << std::endl;
    std::cout << "inst_count = " << Log.state.inst_count << std::endl;
    std::cout << "rf = {" << std::endl;
    std::cout << "  " <<
      "[01] (ra) = " << Log.state.rf_x01_ra << "; " <<
      "[02] (sp) = " << Log.state.rf_x02_sp << "; " <<
      "[03] (gp) = " << Log.state.rf_x03_gp << "; " <<
      "[04] (tp) = " << Log.state.rf_x04_tp << std::endl;
    std::cout << "  [05-07] (t0-t2)     = " <<
      Log.state.rf_x05_t0 << "; " <<
      Log.state.rf_x06_t1 << "; " <<
      Log.state.rf_x07_t2 << std::endl;
    std::cout << "  [08-09] (s0_fp, s1) = " <<
      Log.state.rf_x08_s0_fp << "; " <<
      Log.state.rf_x09_s1 << std::endl;
    std::cout << "  [10-17] (a0-a7)     = " <<
      Log.state.rf_x10_a0 << "; " <<
      Log.state.rf_x11_a1 << "; " <<
      Log.state.rf_x12_a2 << "; " <<
      Log.state.rf_x13_a3 << "; " <<
      Log.state.rf_x14_a4 << "; " <<
      Log.state.rf_x15_a5 << "; " <<
      Log.state.rf_x16_a6 << "; " <<
      Log.state.rf_x17_a7 << std::endl;
    std::cout << "  [18-27] (s2-s11)    = " << Log.state.rf_x18_s2 << "; " <<
      Log.state.rf_x19_s3 << "; " <<
      Log.state.rf_x20_s4 << "; " <<
      Log.state.rf_x21_s5 << "; " <<
      Log.state.rf_x22_s6 << "; " <<
      Log.state.rf_x23_s7 << "; " <<
      Log.state.rf_x24_s8 << "; " <<
      Log.state.rf_x25_s9 << "; " <<
      Log.state.rf_x26_s10 << "; " <<
      Log.state.rf_x27_s11 << std::endl;
    std::cout << "  [28-31] (t3-t6)     = " <<
      Log.state.rf_x28_t3 << "; " <<
      Log.state.rf_x29_t4 << "; " <<
      Log.state.rf_x30_t5 << "; " <<
      Log.state.rf_x31_t6 << std::endl;
    std::cout << "}" << std::endl;
    std::cout <<
      "toIMem = { valid0 = " << Log.state.toIMem_valid0
              << ", data0 = " << Log.state.toIMem_data0 << " };" <<
      "fromIMem = { valid0 = " << Log.state.fromIMem_valid0
              << ", data0 = " << Log.state.fromIMem_data0 << " }" << std::endl;
    std::cout <<
      "toDMem = { valid0 = " << Log.state.toDMem_valid0
              << ", data0 = " << Log.state.toDMem_data0 << " };" <<
      "fromDMem = { valid0 = " << Log.state.fromDMem_valid0
              << ", data0 = " << Log.state.fromDMem_data0 << " }" << std::endl;
    std::cout <<
      "f2d    = { valid0 = " << Log.state.f2d_valid0
              << ", data0 = " << Log.state.f2d_data0 << " };" <<
      "f2dprim  = { valid0 = " << Log.state.f2dprim_valid0
              << ", data0 = " << Log.state.f2dprim_data0 << " }" << std::endl;
    std::cout <<
      "d2e    = { valid0 = " << Log.state.d2e_valid0
              << ", data0 = " << Log.state.d2e_data0 << " };" <<
      "e2w      = { valid0 = " << Log.state.e2w_valid0
              << ", data0 = " << Log.state.e2w_data0 << " }" << std::endl;
#endif
  }

public:
  explicit rv_core(const std::string& elf_fpath) : simulator{} {
    extfuns.imem.read_elf(elf_fpath);
    extfuns.dmem.read_elf(elf_fpath);
  }
};

#ifdef SIM_MINIMAL
template simulator::state_t cuttlesim::init_and_run<simulator>(unsigned long long);
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
// flycheck-clang-include-path: ("../_objects/rv32.v/")
// flycheck-clang-language-standard: "c++17"
// End:
