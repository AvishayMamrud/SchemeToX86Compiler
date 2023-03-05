# SchemeToX86Compiler
a compiler programmed in ocaml. compiles scheme to x86 assembly.
worked and ran it on a linux VM (ubuntu image).

1. i run this compiler via UTOP.
2. you need to execute the command '#use "compiler.ml";;' so you can use its methods.
3. then you have a few options:
  + to get the Reader's output (a s-expression AST) run the line 'Reader.nt_sexpr "<scheme_string>" 0'
  + to get the tag-parser's output (a scheme AST) run the line 'Tag_Parser.tag_parse (Reader.nt_sexpr "<scheme_string>" 0).found'
  + to get the semantic-analyser's output (a scheme AST with the addition of Lexical Environments, Tail Position Calls and Auto Boxing for variables that require it) run the line 'Semantic_Analysis.semantics (Tag_Parser.tag_parse (Reader.nt_sexpr "<scheme_string>" 0).found);;'
  + to compile a scheme file run the line 'compile_scheme_file "<source_file_name>.scm" "<output_file_name>.asm";;'
  + to compile a scheme string run the line 'compile_scheme_string "<output_file_name>.asm" "<scheme_string>";;'
4. if you compiled a file or a string you may now run the assembler to get an executable file:
  + exit the UTOP process (ctrl+D)
  + run the line 'make <output_file_name>' with the same file name you provided to the compilation function (no extension this time).
  + execute the executable file with the line './<output_file_name>' (the exe file has the same name. makefile magic!)
  
  
## thanks o lot!!!
