#!/bin/bash

# Read LaTeX code from stdin
latex_code=$(cat)

# Wrap LaTeX code with necessary tags
wrapped_latex=$(cat <<EOF
\\documentclass{article}
\\begin{document}
\\[
$latex_code
\\]
\\end{document}
EOF
)

# Create a temporary directory
tmp_dir=$(mktemp -d)

# Set up paths
latex_file="${tmp_dir}/math.tex"
pdf_file="${tmp_dir}/math.pdf"

# Write wrapped LaTeX code to a file
echo -e "$wrapped_latex" > "$latex_file"

cat $latex_file

# Compile LaTeX code to PDF
pdflatex -output-directory="$tmp_dir" "$latex_file"

# Open the PDF file with a PDF viewer
zathura "$pdf_file"

# Clean up temporary files
rm -rf "$tmp_dir"
