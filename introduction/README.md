
### compiling introduction_to_lean.pdf

(**NOTE:** The following compilation of introduction_to_lean.pdf never worked.)

To compile the introduction_to_lean.pdf, I did the following:

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

------------------------------------------------

### overview.lean

**Useful commands:** `C-c C-b`, `C-c C-x`, `C-c C-r`

To execute the commands in the file `overview.lean`, load the file into emacs and then run
`C-c C-b` to see the results inline, or `C-c C-x` to execute the file in stand-alone mode.

If you notice that hover-over is no longer working when you move the mouse over the `#check` 
command, then try `C-c C-r` to re-read (re-typecheck) the file.


