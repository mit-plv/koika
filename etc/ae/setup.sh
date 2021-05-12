#!/usr/bin/env sh
# Run this with sudo

apt-get -y install \
        build-essential gcc make perl flex bison \
		pkg-config make patch unzip git aspcud curl emacs \
		autoconf libgmp-dev m4 opam python3 python3-pip yosys \
		gcc gdb g++-9 g++-10 clang clang-format libboost-dev verilator python3-tk \
		libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev

pip3 install numpy matplotlib scipy

export OPAMYES=true
echo '* OPAM init'
opam init --auto-setup --compiler=4.07.1
eval $(opam env)
echo '* OPAM repo add'
opam repo add --all-switches coq-released https://coq.inria.fr/opam/released
echo '* OPAM update'
opam update
echo '* OPAM install (will take a while; maybe 30 minutes)'
opam install -j2 base=v0.12.2 coq=8.10.2 coq-ltac2=0.3 core=v0.12.4 dune=2.7.1 hashcons=1.3 parsexp=v0.12.0 stdio=v0.12.0 zarith=1.9.1

wget -O /tmp/riscv.tgz https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/download/v8.3.0-1.1/xpack-riscv-none-embed-gcc-8.3.0-1.1-linux-x64.tgz
mkdir -p ~/.local/bin/
(cd ~/.local/bin/ && tar -xzf /tmp/riscv.tgz)
echo 'PATH=~/.local/bin/xPacks/riscv-none-embed-gcc/8.3.0-1.1/bin/:$PATH' >> ~/.profile

mkdir -p ~/.emacs.d/
cat > ~/.emacs.d/init.el <<-EOS
    (add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

    (require 'package)
    (add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
    (package-initialize)

    ;; Basic usability
    (xterm-mouse-mode)
    (load-theme 'tango t)

    (setq-default proof-splash-seen t
	              inhibit-startup-screen t)
    (add-to-list 'default-frame-alist '(fullscreen . maximized))
EOS

emacs --batch --load ~/.emacs.d/init.el --eval "(progn (package-refresh-contents) (package-install 'proof-general))"

cd ~
git clone https://github.com/cpitclaudel/verilator.git
cd verilator; autoconf; ./configure; make -j3
sudo make install

mkdir ~/cuttlesim
cd ~/cuttlesim
git clone https://github.com/mit-plv/koika.git -b asplos2021 koika

cd koika

# 9acd9f3a39e3ec15fc254156785c4596096ebd16
git worktree add ../koika_bthom-bp asplos2021-bthom-bp
# 2b72b5f47630d6a139d17cd92897a737eeefaec3
git worktree add ../koika_sim-multicore asplos2021-sim-multicore

cd ~/cuttlesim/koika/examples/rv; make DUT=rv32i; make DUT=rv32e
cd ~/cuttlesim/koika_bthom-bp/examples/rv; make DUT=rv32i
cd ~/cuttlesim/koika_sim-multicore/examples/dynamic_isolation/; make DUT=rv32i_no_sm
