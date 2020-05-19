/*! C++ driver for rv32i simulation with Cuttlesim !*/
#include <iostream>
#include <optional>

#include "rv32.hpp"
#include "elf.hpp"
#include "cuttlesim.hpp"

#define LOG_NUM_SETS 12
#define LOG_TAG_SZ 18

#define NUM_SETS (static_cast<std::size_t>(1) << LOG_NUM_SETS)

#define DMEM_SIZE (static_cast<std::size_t>(1) << 25)

#define SRAM_SIZE (static_cast<std::size_t>(1) << LOG_NUM_SETS)

#define MEM_DEBUG 0

bool core0_done = false;
bool core1_done = false;

bool get_core_done(int core_id) {
  return (core_id ? core1_done : core0_done);
}

void set_core_done(int core_id) {
  if (core_id) {
    core1_done = true;
  } else {
    core0_done = true;
  }
}

struct bookkeeping {
  std::array<std::array<struct_Bookkeeping_row, 4>, NUM_SETS> container;

  int encode_cache (bits<1> core_id, enum_cache_type cache_type) {
	  return (2 * core_id.v + (cache_type == enum_cache_type::dmem ? 1 : 0));
  }

  struct_Bookkeeping_row get(bits<1> core_id, enum_cache_type cache_type, bits<12> idx) {
	  return container[idx.v][encode_cache(core_id, cache_type)];
  }

  void set(bits<1> core_id, enum_cache_type cache_type, bits<12> idx, struct_Bookkeeping_row row) {

#if MEM_DEBUG
	printf("Set core %d, cache %d, idx 0x%x, tag 0x%x, state %d\n", core_id.v, cache_type, idx.v, row.tag.v, row.state);

#endif // MEM_DEBUG
	container[idx.v][encode_cache(core_id,cache_type)] = row;
  }

  struct_maybe_Bookkeeping_row getset(struct_bookkeeping_input input) {
	if (input.book.valid) {
	  set(input.core_id, input.cache_type, input.idx, input.book.data);
	  return struct_maybe_Bookkeeping_row {
	    .valid = bits<1>{false},
        .data =	struct_Bookkeeping_row {
				  .state = enum_MSI::I,
                  .tag = bits<18>{0}
                }
      };
    } else {
	  return struct_maybe_Bookkeeping_row {
	    .valid = bits<1>{true},
        .data =	get(input.core_id, input.cache_type, input.idx)
      };
    }
  }

  bookkeeping() : container{} {}
};

struct sram {
  std::unique_ptr<struct_cache_row[]> mem;
  std::optional<struct_ext_cache_mem_req> last;
  int core_id;

  std::optional<struct_ext_cache_mem_resp> get(bool enable) {
    if (!enable || !last.has_value() || get_core_done (core_id))
      return std::nullopt;
    auto data = last->data;
    auto tag = last->tag;
    auto index = last->index;
    auto newFlag = last->MSI;
    //auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> addr = (prims::widen<32>(tag) << 14) | (prims::widen<32>(index) << 2);

    struct_cache_row current;

#if MEM_DEBUG
    printf("Core %d; Req: dEn 0x%x; data 0x%x; tag: 0x%x; index: 0x%x; addr:0x%x; flag_valid: %d; flag: %d\n", core_id, dEn.v, data.v, tag.v, index.v, addr.v, newFlag.valid, newFlag.data);
#endif // MEM_DEBUG
    if ((addr.v == 0x40001000 || addr.v == 0x80001000) && dEn.v == 0xf) {
      int exitcode = last->data.v;
      if (exitcode == 0) {
        printf("  [0;32mPASS[0m\n");
      } else {
        printf("  [0;31mFAIL[0m (%d)", exitcode);
      }
      set_core_done(core_id);
      printf("Core %d done\n", core_id);

      if (core0_done && core1_done) {
        std::exit(exitcode);
      } else {
        return std::nullopt;
      }
    } else {
      current = mem[index.v];

      if (dEn.v != 0x0) { /* store */
        bits<32> new_data = bits<32>{
          ((dEn[2'0_d] ? data : current.data) & 0x32'000000ff_x) |
          ((dEn[2'1_d] ? data : current.data) & 0x32'0000ff00_x) |
          ((dEn[2'2_d] ? data : current.data) & 0x32'00ff0000_x) |
          ((dEn[2'3_d] ? data : current.data) & 0x32'ff000000_x)
        };

        mem[index.v].tag = tag;
        mem[index.v].data = new_data;
      }

      mem[index.v].flag = newFlag.valid ? newFlag.data : current.flag;

    }

    last.reset();

#if MEM_DEBUG
    printf("Core %d; Resp: tag: 0x%x; data: 0x%x; MSI_state: %d\n", core_id, current.tag.v, current.data.v, current.flag);
#endif // MEM_DEBUG

    return std::optional<struct_ext_cache_mem_resp>{
        struct_ext_cache_mem_resp{.row = current}
      };
  }

  bool put(std::optional<struct_ext_cache_mem_req> req) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_cache_mem_output getput(struct_cache_mem_input req) {
    bool put_ready = put(req.put_valid ? std::optional<struct_ext_cache_mem_req>{req.put_request} : std::nullopt);
    std::optional<struct_ext_cache_mem_resp> get_response = get(bool(req.get_ready));
    return struct_cache_mem_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(struct_ext_cache_mem_resp{})
    };
  }

  void read_elf(const std::string& elf_fpath) {
    elf_load(reinterpret_cast<uint32_t*>(mem.get()), elf_fpath.c_str());
  }

  // Use new … instead of make_unique to avoid 0-initialization
  sram(int id) : mem{std::make_unique<struct_cache_row[]>(SRAM_SIZE)}, last{}, core_id{id} {}

};

struct bram {
  std::unique_ptr<bits<32>[]> mem;
  std::optional<struct_mem_req> last;

  std::optional<struct_mem_resp> get(bool enable) {
    if (!enable || !last.has_value())
      return std::nullopt;

    auto data = last->data;
    auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> current = bits<32>{0};

#if MEM_DEBUG
    printf("MainReq: dEn 0x%x; data 0x%x; addr:0x%x\n", dEn.v, data.v, addr.v);
#endif // MEM_DEBUG

    if ((addr.v == 0x40001000 || addr.v == 0x80001000) && dEn.v == 0xf) {
      int exitcode = last->data.v;
      if (exitcode == 0) {
        printf("  [0;32mPASS[0m\n");
      } else {
        printf("  [0;31mFAIL[0m (%d)", exitcode);
      }
      std::exit(exitcode);
    } else if (addr.v == 0x40001000 || addr.v == 0x80001000) {

    } else {
      current = mem[addr.v >> 2];
      mem[addr.v >> 2] =
        ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
        ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
        ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
        ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);

      // If store, return nothing
    }

    last.reset();

    if (dEn.v == 0x0) {
#if MEM_DEBUG
      printf("MainResp: byte_en: 0x%x; addr: 0x%x; data: 0x%x\n", dEn.v, addr.v, current.v);
#endif // MEM_DEBUG

      return std::optional<struct_mem_resp>{{
        .byte_en = dEn, .addr = addr, .data = current
      }};
    }

    printf("MainStore: return nothing\n");
    return std::optional<struct_mem_resp>{std::nullopt};

  }

  bool put(std::optional<struct_mem_req> req) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_mem_output getput(struct_mem_input req) {
    std::optional<struct_mem_resp> get_response = get(bool(req.get_ready));
    bool put_ready = put(req.put_valid ? std::optional<struct_mem_req>{req.put_request} : std::nullopt);
    return struct_mem_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(struct_mem_resp{})
    };
  }

  void read_elf(const std::string& elf_fpath) {
    elf_load(reinterpret_cast<uint32_t*>(mem.get()), elf_fpath.c_str());
  }

  // Use new … instead of make_unique to avoid 0-initialization
  bram() : mem{new bits<32>[DMEM_SIZE]}, last{} {}
};

struct extfuns_t {
  sram dmem0, dmem1, imem0, imem1;
  bram mainmem;
  bits<1> led;
  bookkeeping ppp_bookkeeping;

  struct_cache_mem_output ext_cache_dmem0(struct_cache_mem_input req) {
    return dmem0.getput(req);
  }

  struct_cache_mem_output ext_cache_dmem1(struct_cache_mem_input req) {
    return dmem1.getput(req);
  }

  struct_cache_mem_output ext_cache_imem0(struct_cache_mem_input req) {
    return imem0.getput(req);
  }

  struct_cache_mem_output ext_cache_imem1(struct_cache_mem_input req) {
    return imem1.getput(req);
  }

  struct_mem_output ext_mainmem(struct_mem_input req) {
    return mainmem.getput(req);
  }

  bits<1> ext_uart_write(struct_maybe_bits_8 req) {
    if (req.valid) {
      putchar(static_cast<char>(req.data.v));
    }
    return req.valid;
  }

  struct_maybe_bits_8 ext_uart_read(bits<1> req) {
    bool valid = req.v;
    return struct_maybe_bits_8 {
      .valid = bits<1>{valid},
      .data = bits<8>{(bits_t<8>)(valid ? getchar() : 0)} };
  }

  bits<1> ext_led(struct_maybe_bits_1 req) {
    bits<1> current = led;
    if (req.valid) {
      led = req.data;
      fprintf(stderr, led.v ? "☀" : "🌣");
    }
    return current;
  }

  struct_maybe_Bookkeeping_row ext_ppp_bookkeeping(struct_bookkeeping_input req) {
	return ppp_bookkeeping.getset(req);
  }

  extfuns_t() : dmem0{sram(0)}, dmem1{sram(1)}, imem0{sram(0)}, imem1{sram(1)},
                mainmem{}, led{false}, ppp_bookkeeping{} {}
};

class rv_core final : public module_rv32<extfuns_t> {
  void strobe(std::uint_fast64_t _unused ncycles) const {
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
  explicit rv_core(const std::string& elf_fpath) : module_rv32{} {
    //extfuns.imem.read_elf(elf_fpath);
    //extfuns.dmem.read_elf(elf_fpath);
    extfuns.mainmem.read_elf(elf_fpath);
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
// flycheck-clang-include-path: ("../_objects/rv32i.v/")
// flycheck-clang-language-standard: "c++17"
// End:
