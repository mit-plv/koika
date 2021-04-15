#!/usr/bin/env python3
from collections import defaultdict
import os
import re
import subprocess
import sys

# DIR = os.path.dirname(os.path.realpath(__file__))

EMACS_LINE_RE = re.compile("(-[*]-.*-[*]-)")
HEADER_BODY_RE = r" *((?P<category>.*?) *\| *)?(?P<docstring>.*?) *"
SHELL_HEADER_RE = re.compile(r"^##" + HEADER_BODY_RE + "$")
ML_HEADER_RE = re.compile(r"^[/(][*]!" + HEADER_BODY_RE + "![*][/)]$")
C_HEADER_RE = re.compile(r"^[/][*]!" + HEADER_BODY_RE + "![*][/]$")
LISP_HEADER_RE = re.compile(r"^;;;" + HEADER_BODY_RE + "$")
HEADER_RE = {
    '.v': ML_HEADER_RE,
    '.ml': ML_HEADER_RE,
    '.lv': LISP_HEADER_RE,
    '.bsv': C_HEADER_RE,
    '.cpp': C_HEADER_RE,
    '.hpp': C_HEADER_RE,
    '.sh': SHELL_HEADER_RE,
    '.py': SHELL_HEADER_RE,
}
KNOWN_EXTENSIONS = HEADER_RE.keys()
SPECIAL_FILES = {
    'etc/configure': SHELL_HEADER_RE
}

class File:
    def __init__(self, fpath):
        self.fpath = fpath
        m = File.find_header(fpath)
        self.category = m and m.group("category")
        self.docstring = m and m.group("docstring")
        self.path = fpath.strip(os.path.sep).split(os.path.sep)

    @staticmethod
    def find_header(fpath):
        try:
            with open(fpath, mode='r') as f:
                headers = [next(f), next(f)]
        except FileNotFoundError:
            headers = []
        header_re = SPECIAL_FILES.get(fpath) or HEADER_RE[os.path.splitext(fpath)[1]]
        for h in headers:
            m = header_re.match(EMACS_LINE_RE.sub("", h))
            if m:
                return m
        return None

class category(str):
    pass

class directory(str):
    pass

class file(str):
    pass

def insert_path(fobj, offset, tree):
    head = fobj.path[offset]
    if offset >= len(fobj.path) - 1:
        if fobj.category:
            tree = tree[category(fobj.category)]
        tree[file(head)] = fobj
    else:
        insert_path(fobj, offset + 1, tree[directory(head)])

def filter(elements, type):
    return sorted(x for x in elements if isinstance(x, type))

KOIKA_RE = re.compile("[kK][oô]ika")

BASE_INDENT = '   '
def serialize_tree(node, indent=''):
    if isinstance(node, dict):
        subindent = BASE_INDENT + indent
        directories = filter(node, directory)
        categories = filter(node, category)
        files = filter(node, file)
        for d in directories:
            yield f"{indent}``{d}/``"
            yield from serialize_tree(node[d], subindent)
        for c in categories:
            yield f"{indent}({c})"
            yield from serialize_tree(node[c], subindent)
        for f in files:
            fobj = node[f]
            if fobj.docstring:
                doc = KOIKA_RE.sub("|koika|", fobj.docstring)
                yield f"{indent}- |{fobj.fpath}|_: {doc}"
            else:
                print(f"!! No documentation for {fobj.fpath}", file=sys.stderr)
        yield ""
        assert set(node) == set(directories + categories + files)

def ddict():
    return defaultdict(ddict)

EXCLUDED = {
    "etc/package.sh",
    "etc/readme/update.py",
    "examples/fft.v.etc/GenerateTwiddle.bsv",
    "examples/fft.v.etc/MiscTypes.bsv",
    "examples/fft.v.etc/driver.cpp",
    "examples/fft.v.etc/mkfft.v",
    "examples/fft.v.etc/mkfft_verilator.cpp",
    "examples/fir.v.etc/driver.cpp",
    "examples/fir.v.etc/mkfir.v",
    "examples/fir.v.etc/mkfir_verilator.cpp",
    "examples/rv/etc/bsv/BRAM2BELoad.v",
    "examples/rv/etc/bsv/SizedFIFO.v",
    "examples/rv/etc/bsv/rv32_bsv/BRAM2BELoad.v",
    "examples/rv/etc/bsv/rv32_bsv/Ehr.bsv",
    "examples/rv/etc/bsv/rv32_bsv/FIFO2.v",
    "examples/rv/etc/bsv/rv32_bsv/FIFOL1.v",
    "examples/rv/etc/bsv/rv32_bsv/Glue_types.bsv",
    "examples/rv/etc/bsv/rv32_bsv/RF.bsv",
    "examples/rv/etc/bsv/rv32_bsv/RevertReg.v",
    "examples/rv/etc/bsv/rv32_bsv/Scoreboard.bsv",
    "examples/rv/etc/bsv/rv32_bsv/SizedFIFO.v",
    "examples/rv/etc/bsv/rv32_bsv/Util.bsv",
    "examples/rv/etc/bsv/rv32_bsv/gen.sh",
    "examples/rv/etc/bsv/rv32_bsv/rv32_bsv.bsv",
    "examples/rv/etc/bsv/rv32_bsv/rv32_bsv.v",
    "examples/rv/etc/bsv/rv32_bsv/top_bsv.bsv",
    "examples/rv/etc/bsv/rv32_bsv/top_bsv.v",
    "examples/rv/etc/bsv/top.v",
    "examples/rv/etc/bsv/top_fpga.v",
    "examples/rv/etc/bsv/wrappers/Glue_types.bsv",
    "examples/rv/etc/bsv/wrappers/gen.sh",
    "examples/rv/etc/bsv/wrappers/rv32.bsv",
    "examples/rv/etc/bsv/wrappers/top.bsv",
    "examples/rv/etc/bsv/wrappers/top_fpga.bsv",
    "examples/rv/etc/nangate45/retiming/multisize.v",
    "examples/rv/etc/sv/ext_finish.v",
    "examples/rv/etc/sv/ext_host_id.v",
    "examples/rv/etc/sv/ext_mem_dmem.v",
    "examples/rv/etc/sv/ext_mem_imem.v",
    "examples/rv/etc/sv/uart.v",
    "examples/rv/tests/elf2hex/ElfFile.cpp",
    "examples/rv/tests/elf2hex/ElfFile.hpp",
    "examples/rv/tests/elf2hex/elf2hex.cpp",
    "examples/rv/tests/run.sh",
    "examples/save_restore.v.etc/save_restore.cpp",
    "tests/trivial_state_machine.etc/fA.v",
    "tests/trivial_state_machine.etc/fB.v",
}

def collect_files():
    files = subprocess.check_output(["git", "ls-files"], encoding="utf-8")
    for f in files.splitlines():
        if f in EXCLUDED:
            # print(f"README.rst: Skipping excluded file {f}")
            EXCLUDED.remove(f)
        elif os.path.splitext(f)[1] in KNOWN_EXTENSIONS or f in SPECIAL_FILES:
            yield File(f)
    if EXCLUDED:
        print(f"README.rst: Some excluded files are not in the repo: {EXCLUDED}")

def build_tree(files):
    tree = ddict()
    for f in files:
        insert_path(f, 0, tree)
    return tree

def serialize_trailer(files):
    for f in files:
        yield f".. |{f.fpath}| replace:: ``{f.path[-1]}``"
        yield f".. _{f.fpath}: {f.fpath}"

BLOCK_START = ".. begin repo architecture"
BLOCK_END = ".. end repo architecture"
BLOCK_RE = re.compile(re.escape(BLOCK_START) + "[^\0]+" + re.escape(BLOCK_END))

def main():
    if not os.path.exists(".git"):
        print("README.rst: Not in a git clone, skipping README update.")
        return
    files = list(collect_files())
    tree = "\n".join(serialize_tree(build_tree(files)))
    trailer = "\n".join(serialize_trailer(files))
    if len(sys.argv) > 0:
        with open(sys.argv[1], mode="r") as old:
            contents = old.read()
        repl = f"{BLOCK_START}\n\n{tree}\n{trailer}\n{BLOCK_END}"
        contents = BLOCK_RE.sub(repl, contents)
        with open(sys.argv[1], mode='w') as new:
            new.write(contents)
    else:
        print(tree)

if __name__ == '__main__':
    main()
