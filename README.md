# Notes on Learning Lean

# Intallation

On Ubuntu 16.04 I installed Lean from source following the directions
here:


## Lean in Emacs

From the `lean/bin` directory, run the command `leanemacs_build`

### Emacs Key Bindings and Commands

| Key                | Function                                                                        |
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
