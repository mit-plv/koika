#!/usr/bin/env bash
## Set up a Vagrant VM for Kôika development
# To set up a non-vagrant VM, run as follows:
# USERNAME=$USER LOGFILE=~/provision.log sudo --preserve-env ./provision.sh

export DEBIAN_FRONTEND=noninteractive
: "${LOGFILE:=/vagrant/provision.log}"
: "${USERNAME=vagrant}"

touch $LOGFILE
chown $USERNAME $LOGFILE
echo "* Starting; see $LOGFILE for details."

echo ""
echo '************************************'
echo '***   Installing base packages   ***'
echo '************************************'

echo '* apt-get update'
apt-get -y update >> $LOGFILE 2>&1
echo '* apt-get install (needs to download about 150MB of archives)'
apt-get -y install \
		pkg-config make patch unzip git aspcud curl emacs \
		autoconf libgmp-dev m4 opam python3 python3-pip yosys \
		gcc gdb clang clang-format libboost-dev verilator python3.6-tk \
		libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev \
	>> $LOGFILE 2>&1

sudo su $USERNAME <<-EOF
	cat > ~/gui-setup.sh <<-EOS
		#!/usr/bin/env bash
		apt-get -y install lubuntu-desktop

		su $USERNAME <<-EOEOS
			mkdir -p ~/.fonts
			wget -O ~/.fonts/symbola-monospace.ttf https://raw.githubusercontent.com/cpitclaudel/monospacifier/master/fonts/Symbola_monospacified_for_UbuntuMono.ttf
			wget -O /tmp/ubuntu-fonts.zip http://font.ubuntu.com/download/ubuntu-font-family-0.83.zip
			unzip /tmp/ubuntu-fonts.zip -d ~/.fonts/
			fc-cache
		EOEOS
	EOS
	chmod +x ~/gui-setup.sh

	cat >> ~/.profile <<< 'export TERM=xterm-256color'

	echo ""
	echo '************************************'
	echo '***   Downloading OPAM packages  ***'
	echo '************************************'

	export OPAMYES=true
	echo '* OPAM init'
	opam init --auto-setup --compiler=4.07.0 >> $LOGFILE 2>&1
	eval \$(opam env)
	echo '* OPAM repo add'
    opam repo add --all-switches coq-released https://coq.inria.fr/opam/released >> $LOGFILE 2>&1
	echo '* OPAM update'
    opam update >> $LOGFILE 2>&1
	echo '* OPAM install (will take a while; maybe 30 minutes)'
    opam install -j2 base=v0.12.2 coq=8.10.2 coqide=8.10.2 coq-ltac2=0.3 core=v0.12.4 dune=1.11.4 hashcons=1.3 parsexp=v0.12.0 stdio=v0.12.0 zarith=1.9.1 >> $LOGFILE 2>&1

	echo ""
	echo '************************************'
	echo '***    Downloading RISCV deps    ***'
	echo '************************************'

	echo '* GCC download'
	wget -q -O /tmp/riscv.tgz https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/download/v8.3.0-1.1/xpack-riscv-none-embed-gcc-8.3.0-1.1-linux-x64.tgz
	echo '* GCC setup'
	mkdir -p ~/.local/bin/ >> $LOGFILE 2>&1
	(cd ~/.local/bin/ && tar -xzf /tmp/riscv.tgz) >> $LOGFILE 2>&1
	echo 'PATH=~/.local/bin/xPacks/riscv-none-embed-gcc/8.3.0-1.1/:\$PATH' >> ~/.profile
	echo '* PyVerilator'
	pip3 install --user git+https://github.com/csail-csg/pyverilator >> $LOGFILE 2>&1

	echo ""
	echo '************************************'
	echo '***   Setting up Proof General   ***'
	echo '************************************'

	mkdir -p ~/.emacs.d/
	cat > ~/.emacs.d/init.el <<-EOS
		(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

		(require 'package)
		(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
		(package-initialize)

		;; Load company-coq when opening Coq files
		(add-hook 'coq-mode-hook #'company-coq-mode)

		;; Terminal keybindings
		(with-eval-after-load 'company-coq
		  (define-key company-coq-map (kbd "C-c RET") #'company-coq-proof-goto-point)
		  (define-key company-coq-map (kbd "C-c C-j") #'company-coq-proof-goto-point))

		;; Font fallback
		(when (functionp 'set-fontset-font)
		  (set-face-attribute 'default nil :family "Ubuntu Mono")
		  (set-fontset-font t 'unicode (font-spec :name "Ubuntu Mono"))
		  (set-fontset-font t 'unicode (font-spec :name "Symbola monospacified for Ubuntu Mono") nil 'append))

		;; Basic usability
		(xterm-mouse-mode)
		(load-theme 'tango-dark t)
	EOS

	echo '* package install'
	emacs --batch --load ~/.emacs.d/init.el \
		--eval "(progn (package-refresh-contents) (package-install 'proof-general) (package-install 'company-coq))" >> $LOGFILE 2>&1

	echo ""
	echo '************************************'
	echo '***        Setup complete        ***'
	echo '************************************'

	echo ""
	echo Log into the VM using ‘vagrant ssh’.
    echo You can now run ‘sudo \~/gui-setup.sh’ in the VM to install a GUI, or start using Coq straight away.
EOF

# Local Variables:
# indent-tabs-mode: t
# End:
