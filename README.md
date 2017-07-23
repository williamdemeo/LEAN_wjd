# LEAN_wjd

Personal notes accumulated in the process of learning
the [Lean Theorem Prover](http://leanprover.github.io/).

*The contents of this repository are not intended for public consumption.*

## Background and Motivation

The [Lean Theorem Prover](http://leanprover.github.io/) aims to bridge the gap 
between interactive and automated theorem proving, by situating automated tools 
and methods in a framework that supports user interaction and the construction 
of fully specified axiomatic proofs. 

Lean's underlying logic has a computational interpretation, and Lean can be viewed
equally well as a programming language. More to the point, it can be viewed as a
system for writing programs with a precise semantics, as well a reasoning about
the functions that the programs compute. 

Lean also has mechanisms to serve as its own *metaprogramming language*, which 
means that one can implement automation and extend the functionality of Lean using 
Lean itself. Metaprogramming aspects of Lean are explored in the tutorial
[Programming in Lean](https://leanprover.github.io/programming_in_lean).


## Intallation of Lean

On Ubuntu 16.04 I installed Lean from source following the directions
here:

https://github.com/leanprover/lean/blob/master/doc/make/ubuntu-16.04.md

To summarize the installation process, assuming you have the necessary dependencies, you do the following:

    git clone https://github.com/leanprover/lean.git
    cd lean
    mkdir -p build/release
    cd build/release
    cmake ../../src
    make

---------------------------------

## A first Lean session in Emacs

In the Lean repository that you cloned above, go into the directory called `lean/bin`, then run the command `leanemacs_build`.

After launching emacs this way, open a new file called `check.lean` and 
put `#check id` on the first line.  Then hover over the word "check." 
You should be shown the type of the `id` function.

To view the output of commands such as `check` and `print` in the emacs buffer, enable this feature with the key sequence `C-c C-b`.

### Making things permanent
You can include `lean-mode` permanently in your emacs init file by putting 
some code in your Emacs init file (typically `~/.emacs.d/init.el`).

If you already have the dependencies installed, it should suffice
to add the following three lines to your `init.el` file:

    (setq lean-rootdir "~/projects/lean")
    (setq load-path (cons "~/projects/lean/src/emacs" load-path))
    (require 'lean-mode)

Otherwise, add the following to your `init.el` file:

    ;; You need to modify the following two lines:
    (setq lean-rootdir "~/projects/lean")
    (setq lean-emacs-path "~/projects/lean/src/emacs")

    (setq lean-mode-required-packages '(company dash dash-functional f
                               flycheck let-alist s seq))

    (require 'package)
    (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
    (package-initialize)
    (let ((need-to-refresh t))
      (dolist (p lean-mode-required-packages)
        (when (not (package-installed-p p))
          (when need-to-refresh
            (package-refresh-contents)
            (setq need-to-refresh nil))
          (package-install p))))

    (setq load-path (cons lean-emacs-path load-path))

    (require 'lean-mode)



### Emacs Key Bindings and Commands

| Key Binding      | Function                                                                        |
|--------------------|---------------------------------------------------------------------------------|
| <kbd>M-.</kbd>     | jump to definition in source file (`lean-find-definition`)                      |
| <kbd>S-SPC</kbd>   | auto complete identifiers, options, imports, etc. (`company-complete`)          |
| <kbd>C-c C-k</kbd> | shows the keystroke needed to input the symbol under the cursor                 |
| <kbd>C-c C-x</kbd> | execute lean in stand-alone mode (`lean-std-exe`)                               |
| <kbd>C-c SPC</kbd> | run a command on the hole at point (`lean-hole`)
| <kbd>C-c C-g</kbd> | toggle showing current tactic proof goal (`lean-toggle-show-goal`)              |
| <kbd>C-c C-n</kbd> | toggle showing next error in dedicated buffer (`lean-toggle-next-error`)        |
| <kbd>C-c C-b</kbd> | toggle showing output in inline boxes (`lean-message-boxes-toggle`)             |
| <kbd>C-c C-r</kbd> | restart the lean server (`lean-server-restart`)                                 |
| <kbd>C-c ! n</kbd> | flycheck: go to next error                                                      |
| <kbd>C-c ! p</kbd> | flycheck: go to previous error                                                  |
| <kbd>C-c ! l</kbd> | flycheck: show list of errors                                                   |

The [introduction](https://github.com/williamdemeo/LEAN_wjd/tree/master/introduction) directory
contains source code accumulated while working through the first 20 pages of the 
(50-page) tutorial 
[An Introduction to Lean](https://leanprover.github.io/introduction_to_lean/introduction_to_lean.pdf).

That tutorial is essentially a 50-page compendium of examples aimed at showing off what 
Lean can do, and after just 12 pages the authors suggest moving on to one of the 
other tutorials. They give the following advice:

*If you are motivated to continue using Lean in earnest, we recommend
continuing, from here, to either of the following more expansive introductions:*

+ **Theorem Proving in Lean** 
  ([online](https://leanprover.github.io/theorem_proving_in_lean), 
  [pdf](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf))

+ **Programming in Lean**
  ([online](https://leanprover.github.io/programming_in_lean/)
  [pdf](https://leanprover.github.io/programming_in_lean/programming_in_lean.pdf))


So let's move on...

The directory [theorem-proving](https://github.com/williamdemeo/LEAN_wjd/tree/master/theorem_proving) collects my notes on, and excerpts from, the pdf tutorial
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf)

