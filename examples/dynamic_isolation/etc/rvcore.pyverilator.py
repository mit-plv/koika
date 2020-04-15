#!/usr/bin/env python3
## Python driver for C++ simulation with Verilator
import argparse
import fnmatch
import subprocess
import os
import sys
from os.path import realpath, relpath, basename, dirname

from pyverilator import PyVerilator

def signal_name(signal):
    return signal.verilator_name

def interact(locals):
    try:
        from IPython.terminal.embed import InteractiveShellEmbed
        InteractiveShellEmbed().mainloop(local_ns=locals)
    except ImportError:
        import code
        code.interact(local=locals)

def vl_finish_callback(sim, *_args):
    sim.finished = True

def init_simulator(top, args):
    try:
        sim = PyVerilator.build(top, build_dir='obj_dir.py',
                                quiet=True, command_args=args,
                                verilog_defines=["BRAM_RUNTIME_INIT", "SIMULATION"])
        sim.set_vl_finish_callback(lambda *args: vl_finish_callback(sim, *args))
        return sim
    except subprocess.CalledProcessError as e:
        stderr = (e.stderr or b"").decode("utf-8")
        stdout = (e.stdout or b"").decode("utf-8")
        print("Compilation failed:\nstderr:\n{}\nstdout:\n{}".format(stderr, stdout))
        sys.exit(1)

class Simulator:
    def __init__(self, top, probes, exit_probes, args):
        self.time = 0
        self.top = top
        self.args = args
        self.sim = init_simulator(top, [sys.argv[0], *args])
        self.probes = sorted(self.gather_signals(probes), key=signal_name)
        self.exit_probes = sorted(self.gather_signals(exit_probes), key=signal_name)

    def tick(self):
        self.sim.io.CLK = 1
        self.sim.io.CLK = 0
        self.time += 1
        self.probe_signals("  ", self.probes, True)

    def reset(self, ncycles=2):
        self.sim.io.CLK = 0
        self.sim.io.RST_N = 0
        self.time = -ncycles
        for _ in range(ncycles):
            self.tick()
        self.sim.io.RST_N = 1

    def gather_signals(self, patterns):
        for pattern in patterns:
            for signal in self.sim.all_signals.values():
                if fnmatch.fnmatch(signal.verilator_name, pattern):
                    yield signal

    def probe_signals(self, indent, signals, print_title):
        if signals:
            if print_title:
                print("#", self.time)
            for signal in signals:
                fmt = "{indent}{name}: {sz}'b{v:0_b} (0x{v:x}, {v})"
                print(fmt.replace("_", str(signal.width)).format(**{
                    "indent": indent,
                    "name": signal.short_name,
                    "sz": signal.width,
                    "v": signal.value
                }))

    def interact(self):
        interact(locals())

    def run(self, ncycles=-1):
        try:
            self.reset()
            while not self.sim.finished and (ncycles < 0 or self.time < ncycles):
                self.tick()
        except KeyboardInterrupt:
            pass
        if self.exit_probes:
            print("  [{}]@[{}]:".format(self.args[0], self.top))
            self.probe_signals("    ", self.exit_probes, False)

def parse_arguments():
    parser = argparse.ArgumentParser(description='PyVerilator driver for the Kôika RISCV processor')
    parser.add_argument("vmh", help="Which memory image (VMH) to load")
    parser.add_argument("ncycles", type=int, default=-1, help="How many cycles to run")
    parser.add_argument("--vtop", help="Which Verilog file to use")
    parser.add_argument("--interact", action='store_true', help="Run interactively")
    parser.add_argument("--probes", metavar="SIGNAL", nargs="+", default=[],
                        help="Print signals on each cycle")
    parser.add_argument("--exit-probes", metavar="SIGNAL", nargs="+", default=[],
                        help="Print signals on exit")
    parser.add_argument("--arg", metavar="ARG", action="append", default=[],
                        help="Pass an argument to verilator")
    return parser.parse_args()

def main():
    args = parse_arguments()

    vdir = dirname(realpath(args.vtop))
    vmh = relpath(args.vmh, vdir)
    os.chdir(vdir)

    sim = Simulator(basename(args.vtop), args.probes,
                    args.exit_probes, ("+VMH=" + vmh, *args.arg))

    if args.interact:
        sim.interact()
    else:
        sim.run(args.ncycles)

if __name__ == '__main__':
    main()
