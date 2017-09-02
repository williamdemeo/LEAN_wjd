First, to compile the introduction_to_lean.pdf, I did the following:

    sudo apt-get install mercurial python2.7 texlive-latex-recommended \
                     texlive-humanities texlive-xetex texlive-science \
                     texlive-latex-extra texlive-fonts-recommended texlive-luatex\
                     bibtex2html git make mercurial autoconf automake gcc curl


    ## CLONE MY FORK OF THE REPO:
    git clone git@github.com:williamdemeo/introduction_to_lean.git
    cd introduction_to_lean

    # CHECKOUT THE mkleanbook SUBMODULE:
	git submodule update --init --recursive

	make install-cask # after this, you need to add the cask binary to your $PATH
	export PATH="home/williamdemeo/.cask/bin:$PATH"
	make install-pygments
	make

