#!/usr/bin/env python3
import re
import sys
import os
from collections import OrderedDict
from typing import *

import numpy as np
import scipy.stats as st
import matplotlib
matplotlib.use('pdf')
from matplotlib import pyplot as plt, patches

CI = False

TIME_MARKER = ">> "
LINE_RE = re.compile(
    "^" + re.escape(TIME_MARKER) +
    "(?P<compiler>.*?)\t"
    "(?P<simulator>.*?)\t"
    "(?P<test>.*?)\t"
    "real: (?P<real>.*?)\t"
    "user: (?P<user>.*?)\t"
    "sys: (?P<sys>.*?)"
    "$")

TYPES = {
    "compiler": str,
    "simulator": str,
    "test": str,
    "real": float,
    "user": float,
    "sys": float
}

def parse(stream: Iterable[str]):
    for (idx, line) in enumerate(stream):
        if line.startswith(TIME_MARKER):
            m = LINE_RE.match(line)
            assert m, "{}: Unrecognized format ({})".format(idx, line)
            yield { k: cast(m.group(k)) for k, cast in TYPES.items() }

def read(fpaths):
    for path in fpaths:
        with open(path) as s:
            yield from parse(s)

Grouped = Dict[str, Dict[str, float]]
def group_measurements(measurements) -> Grouped:
    grouped = {}
    for r in measurements:
        grouped.setdefault(r["compiler"], {}) \
               .setdefault(r["simulator"], {}) \
               .setdefault(r["test"], []) \
               .append(r["real"])
    return grouped

# https://www.statology.org/confidence-intervals-python/
# https://stackoverflow.com/questions/15033511/compute-a-confidence-interval-from-sample-data
class Summary:
    def __init__(self, values, cycles):
        self.values = np.array(list(values))
        self.mean = np.mean(values)
        self.cycles = cycles
        if len(values) > 1:
            self.sem = st.sem(values)
            self.ci95 = st.t.interval(alpha=0.95, df=len(values)-1, loc=self.mean, scale=self.sem)
            self.ci95delta = (self.mean - self.ci95[0], self.ci95[1] - self.mean)
        else:
            self.sem = self.ci95 = np.NaN
            self.ci95delta = (np.NaN, np.NaN)

    @property
    def cps(self):
        return Summary([self.cycles / v for v in self.values], None)

    def __repr__(self):
        return repr(vars(self))

CYCLES = {
    'collatz': 1000000000,
    'fir': 1000000000,
    'fft': 30000000,
    'rv32e-morse': 19503358,
    'rv32i-morse': 19503318,
    'rv32e-primes': 25104574,
    'rv32i-primes': 25099651,
    'rv32i-bp-primes': 23683454,
    'rv32i-mc-primes': 46825434,
    'rv32i-rvbench_median': 60688,
    'rv32i-rvbench_qsort': 82832,
}

def summarize(by_compiler):
    return {compiler:
       {simulator:
        {test: Summary(rs, CYCLES[test]) for test, rs in by_test.items()}
        for simulator, by_test in by_simulator.items()}
       for compiler, by_simulator in by_compiler.items()}

HEX = {"yellow": ("#fce94f", "#edd400", "#c4a000"),
       "orange": ("#fcaf3e", "#f57900", "#ce5c00"),
       "brown":  ("#e9b96e", "#c17d11", "#8f5902"),
       "green":  ("#8ae234", "#73d216", "#4e9a06"),
       "blue":   ("#729fcf", "#3465a4", "#204a87"),
       "purple": ("#ad7fa8", "#75507b", "#5c3566"),
       "red":    ("#ef2929", "#cc0000", "#a40000"),
       "grey":   ("#eeeeec", "#d3d7cf", "#babdb6"),
       "black":  ("#888a85", "#555753", "#2e3436")}

COLORS = {
    "cuttlesim": HEX["orange"][1:],
    "verilator-koika": HEX["blue"][1:],
    "verilator-bluespec": HEX["purple"][1:],
    "cvc": HEX["green"][1:],
    "icarus": HEX["brown"][1:],

    "g++-9": HEX["brown"][0:2],
    "g++-10": HEX["brown"][1:3],
    "clang++-10": HEX["red"][1:3],
}


def rcParams(fontsize=10, **extra):
    matplotlib.rcParams.update({
        "font.size": fontsize,
        # "font.family": "serif",
        # "font.serif": "Iosevka",
        "font.weight": 400,
        "axes.titlesize": "small",
        "axes.labelsize": "small",
        "axes.titleweight": 400,
        "axes.labelweight": 400,
        "xtick.labelsize": "small",
        "ytick.labelsize": "small",
        "legend.fontsize": "small",
        "legend.labelspacing": 0,
        "text.usetex": False,
        "figure.titleweight": 400,
        "savefig.bbox": "tight",
        "savefig.pad_inches": 0.05
    })

    matplotlib.rcParams.update(**extra)

def all_tests(summaries_by_simulator):
    keys = (k for d in summaries_by_simulator.values() for k in d.keys())
    return list(OrderedDict.fromkeys(keys))

def plot1(summaries_by_simulator, ax, cps):
    tests = all_tests(summaries_by_simulator)
    y = np.arange(len(tests))[::-1]
    nbars = len(summaries_by_simulator)
    height = 0.75 / nbars
    legend_patches = []

    delta = - nbars / 2
    for simulator, by_test in summaries_by_simulator.items():
        points = [by_test[t] for t in tests]
        if cps:
            points = [s.cps for s in points]
        x, ci = zip(*((s.mean, s.ci95delta) for s in points))

        medium, dark = COLORS[simulator]

        xerr = {"xerr": np.array(list(ci)).T} if CI else {}
        ax.barh(y - (delta + 0.5) * height, x,
                height=height,
                color=medium,
                log=cps,
                error_kw={ "ecolor": dark, "lw": 0.5,
                           "capsize": 1, "capthick": 0.5 },
                **xerr)
        patch = patches.Patch(facecolor=medium,
                              edgecolor=dark,
                              label=simulator)
        legend_patches.append(patch)
        delta += 1

    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['left'].set_visible(False)
    ax.yaxis.set_tick_params(which="both", pad=5, length=0, rotation=0)
    ax.set_xlabel("Cycles per second, log scale (95% CI)" if cps else "Run time (seconds, 95% CI)")
    # ax.set_ylabel("File")
    ax.set_yticks(y)
    ax.set_yticklabels(list(tests), va="center")
    # ax.autoscale(enable=True, axis='x')

    return legend_patches

def cuttlesim_verilator_1(summaries_by_simulator, cps):
    # from pprint import pprint; pprint(summaries_by_simulator)
    fig, ax = plt.subplots(1, 1, figsize=(3.2, 1.5))
    legend_patches = plot1(summaries_by_simulator, ax, cps)
    ax.legend(handles=legend_patches, loc="lower right" if cps else "upper right")
    fig.tight_layout(pad=0.5)
    return fig

def filter(measurements, compilers, simulators, tests):
    return {c: {s: {t: measurements[c][s][t] for t in tests if t in measurements[c][s]}
                for s in simulators if s in measurements[c]}
            for c in compilers if c in measurements}

def cuttlesim_verilator(measurements):
    data = filter(measurements,
                  ["g++-9"], # FIXME g++-9
                  ["cuttlesim", "verilator-koika"],
                  ["collatz", "fir", "fft", "rv32e-primes", "rv32i-primes",
                   "rv32i-bp-primes", "rv32i-mc-primes"])["g++-9"]
    cuttlesim_verilator_1(data, cps=True).savefig("bench/cuttlesim-verilator-cps.pdf")
    cuttlesim_verilator_1(data, cps=False).savefig("bench/cuttlesim-verilator-wall.pdf")

def koika_bluespec_1(data, cps):
    fig, ax = plt.subplots(1, 1, figsize=(3.2, 1.5))
    legend_patches = plot1(data, ax, cps)
    fig.legend(handles=legend_patches,
               loc="lower center",
               bbox_to_anchor=(0.5, 0),
               ncol=2)
    fig.tight_layout(pad=0.5, rect=(0,0.18,1,1))
    return fig

def koika_bluespec(measurements):
    data = filter(measurements,
              ["g++-9"],
              ["cuttlesim", "verilator-koika", "verilator-bluespec"],
              ["fir", "fft", "rv32i-primes"])["g++-9"]
    koika_bluespec_1(data, True).savefig("bench/koika-bluespec-verilator-cps.pdf")
    koika_bluespec_1(data, False).savefig("bench/koika-bluespec-verilator-wall.pdf")

def gcc_clang(measurements):
    compilers = ["g++-9", "g++-10", "clang++-10"]
    simulators = ["cuttlesim", "verilator-koika"]
    test = "rv32i-primes"
    data = {c: {s: measurements[c][s][test]
                for s in simulators if s in measurements[c]}
            for c in compilers if c in measurements}
    fig, ax = plt.subplots(1, 1, figsize=(3.2, 1))
    legend_patches = plot1(data, ax, False)
    fig.legend(handles=legend_patches,
               loc="lower center",
               bbox_to_anchor=(0.5, 0),
               ncol=3)
    fig.tight_layout(pad=0.5, rect=(0,0.18,1,1))
    fig.savefig("bench/cuttlesim-verilator-wall-gcc-clang.pdf")

def minimal(measurements):
    cps = True
    summaries_by_simulator = \
        filter(measurements,
                  ["g++-9"],
                  ["cuttlesim", "verilator-koika"],
                  ["collatz", "fir", "fft", "rv32e-primes", "rv32i-primes",
                   # "rv32i-bp-primes", "rv32i-mc-primes"])
                   ])["g++-9"]

    fig, ax = plt.subplots(1, 1, figsize=(3.2, 1.5))
    tests = all_tests(summaries_by_simulator)
    y = np.arange(len(tests))[::-1]
    nbars = len(summaries_by_simulator)
    height = 0.75 / nbars
    legend_patches = []

    delta = - nbars / 2
    for simulator, by_test in summaries_by_simulator.items():
        points = [by_test[t] for t in tests]
        if cps:
            points = [s.cps for s in points]
        x, ci = zip(*((s.mean, s.ci95delta) for s in points))

        medium, dark = COLORS[simulator]

        xerr = {"xerr": np.array(list(ci)).T} if not cps else {}

        ax.barh(y - (delta + 0.5) * height, x,
                height=height,
                color=medium,
                log=cps,
                error_kw={ "ecolor": dark, "lw": 0.5,
                           "capsize": 1, "capthick": 0.5 }
                **xerr)
        patch = patches.Patch(facecolor=medium,
                              edgecolor=dark,
                              label=simulator)
        legend_patches.append(patch)
        delta += 1

    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['left'].set_visible(False)
    ax.yaxis.set_tick_params(which="both", pad=5, length=0, rotation=0)
    ax.set_xlabel("Cycles per second, log scale (95% CI)" if cps else "Run time (seconds, 95% CI)")
    # ax.set_ylabel("File")
    ax.set_yticks(y)
    ax.set_yticklabels(list(tests), va="center")
    # ax.autoscale(enable=True, axis='x')

    ax.legend(handles=legend_patches, loc="lower right" if cps else "upper right")
    fig.tight_layout(pad=0.5)
    plt.show()

def main():
    os.makedirs("bench", exist_ok=True)

    rcParams(fontsize=8)

    records = parse(sys.stdin) if len(sys.argv) <= 1 else read(sys.argv[1:])
    measurements = summarize(group_measurements(records))
    # from pprint import pprint; pprint(measurements)

    # minimal(measurements)
    cuttlesim_verilator(measurements)
    koika_bluespec(measurements)
    gcc_clang(measurements)

if __name__ == '__main__':
    main()
