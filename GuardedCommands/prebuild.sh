chmod +x packages/FsLexYacc.7.0.6/build/fslex.exe
chmod +x packages/FsLexYacc.7.0.6/build/fsyacc.exe
mono packages/FsLexYacc.7.0.6/build/fslex.exe Lexer.fsl;
mono packages/FsLexYacc.7.0.6/build/fsyacc.exe --module Parser Parser.fsy