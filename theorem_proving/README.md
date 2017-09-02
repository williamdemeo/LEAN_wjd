# LEAN_wjd

## theorem_proving

This directory collects notes that I took while working through the online book 
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf).


First, to compile the theorem_proving_in_lean.pdf, I did the following:

	## CLONE MY FORK OF THE REPO:
    git clone git@github.com:williamdemeo/theorem_proving_in_lean.git
    cd  theorem_proving_in_lean/


	## MAKE SURE IT'S UP-TO-DATE:
	git remote add upstream git@github.com:leanprover/theorem_proving_in_lean.git
    git fetch upstream
    git checkout master
    git merge upstream/master
	git push origin master

    ## INSTALL THE FOLLOWING REQUIRED PACKAGES:
    sudo apt-get install python3-venv latexmk texlive-xetex

    ## MAKE THE DOCS, ETC
	make install-deps
    sudo pip install --upgrade pip  # (upgrade pip)
    make install-deps
    make html
    make latexpdf
    ./deploy.sh williamdemeo theorem_proving_in_lean

    ## NOW YOU CAN VIEW THE PDF:
	evince _build/latex/theorem_proving_in_lean.pdf &
	
	
