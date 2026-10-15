-- Disegno in Neovim: evidenziazione con tree-sitter, :make con la quickfix.
-- @disegno@ è il comando disegno del flake, sostituito quando si costruisce il plugin.
vim.bo.commentstring = "; %s"
vim.bo.makeprg = "@disegno@ check %"
vim.bo.errorformat = "%f:%l:%c: %m"
vim.bo.lisp = true
pcall(vim.treesitter.start)
