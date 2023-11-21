#!/usr/bin/env sh

set -e

# Read LaTeX code from stdin
latex_code=$(cat)

# Create a temporary directory
tmp_dir=$(mktemp -d)

# Set up paths
latex_file="${tmp_dir}/math.tex"
pdf_file="${tmp_dir}/math.pdf"

cat > "$latex_file" <<EOF
\\documentclass{standalone}
\\usepackage[T1]{fontenc} % https://tex.stackexchange.com/a/181119
\\usepackage[utf8]{inputenc} % https://tex.stackexchange.com/a/181119
\\usepackage{alphabeta}
\\newcommand{\\AppIT}{\\textsc{App}_1}
\\newcommand{\\AppET}{\\textsc{App}_2}
\\newcommand{\\ValueT}{\\textsc{Val}}
\\newcommand{\\CaseIT}{\\textsc{Case}_1}
\\newcommand{\\CaseET}{\\textsc{Case}_2}
\\newcommand{\\LookupT}{\\textsc{Look}}
\\newcommand{\\UpdateT}{\\textsc{Upd}}
\\newcommand{\\BindT}{\\textsc{Bind}}
\\newcommand{\\LetOT}{\\textsc{Let}_0}
\\newcommand{\\LetIT}{\\textsc{Let}_1}
\\begin{document}
\\fboxsep2pt\\fboxrule0pt\\fbox{\$ $latex_code \$}
\\end{document}
EOF


cat $latex_file

# Compile LaTeX code to PDF
pdflatex -output-directory="$tmp_dir" "$latex_file"

# Open the PDF file with a PDF viewer
zathura --mode=fullscreen "$pdf_file"

# Clean up temporary files
rm -rf "$tmp_dir"
