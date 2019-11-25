#!/usr/bin/env python3
from collections import defaultdict
import os
import re
import subprocess
import sys

# DIR = os.path.dirname(os.path.realpath(__file__))

KNOWN_EXTENSIONS = [".ml", ".v", ".lv", ".hpp", ".cpp"]
EMACS_LINE_RE = re.compile("(-[*]-.*-[*]-)")
HEADER_BODY_RE = r" *((?P<category>.*?): *)?(?P<docstring>.*?) *"
ML_HEADER_RE = re.compile(r"^[/(][*]!" + HEADER_BODY_RE + "![*][/)]$")
C_HEADER_RE = re.compile(r"^[/][*]!" + HEADER_BODY_RE + "![*][/]$")
LISP_HEADER_RE = re.compile(r"^;;;" + HEADER_BODY_RE + "$")
HEADER_RE = {
    '.v': ML_HEADER_RE,
    '.ml': ML_HEADER_RE,
    '.lv': LISP_HEADER_RE,
    '.cpp': C_HEADER_RE,
    '.hpp': C_HEADER_RE,
}

class File:
    def __init__(self, fpath):
        try:
            with open(fpath, mode='r') as f:
                header = next(f)
            header = EMACS_LINE_RE.sub("", header)
        except FileNotFoundError:
            header = None
        m = header and HEADER_RE[os.path.splitext(fpath)[1]].match(header)
        self.fpath = fpath
        self.category = m and m.group("category")
        self.docstring = m and m.group("docstring")
        self.path = fpath.strip(os.path.sep).split(os.path.sep)

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
            doc = fobj.docstring
            if doc:
                yield f"{indent}- |{fobj.fpath}|_: {fobj.docstring}"
            else:
                print(f"!! No documentation for {fobj.fpath}", file=sys.stderr)
        yield ""
        assert set(node) == set(directories + categories + files)

def ddict():
    return defaultdict(ddict)

EXCLUDED = [
    "examples/function_call.v.etc/extfuns.hpp",
    "examples/function_call.v.etc/fetch_instr.v",
    "examples/rv/elf2hex/ElfFile.cpp",
    "examples/rv/elf2hex/ElfFile.hpp",
    "examples/rv/elf2hex/elf2hex.cpp",
    "examples/rv/etc/BRAM2BELoad.v",
    "examples/rv/etc/Counter.v",
    "examples/rv/etc/SizedFIFO.v",
    "examples/rv/etc/TopLevel.v",
    "examples/rv/etc/elf.hpp",
    "examples/rv/etc/mkProc.v",
    "ocaml/backends/resources/cuttlesim.cpp",
    "ocaml/backends/resources/verilator.cpp",
    "ocaml/backends/resources/verilator.hpp"]

def collect_files():
    files = subprocess.check_output(["git", "ls-files"], encoding="utf-8")
    for f in files.splitlines():
        if f in EXCLUDED:
            print(f"Skipping excluded file {f}")
        elif os.path.splitext(f)[1] in KNOWN_EXTENSIONS:
            yield File(f)

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
