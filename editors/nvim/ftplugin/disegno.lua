-- Disegno in Neovim: tree-sitter highlighting, :make with the quickfix.
-- @disegno@ is the flake's disegno command, substituted when the plugin is built.
vim.bo.commentstring = "; %s"
vim.bo.makeprg = "@disegno@ check %"
vim.bo.errorformat = "%f:%l:%c: %m"
vim.bo.lisp = true
pcall(vim.treesitter.start)

-- The LSP server is the same binary: disegno lsp (diagnostics while typing, hover, gd, symbols, completion).
vim.lsp.start({
  name = "disegno",
  cmd = { "@disegno@", "lsp" },
  root_dir = vim.fs.root(0, { ".git", "flake.nix" }) or vim.fn.getcwd(),
})
