@echo off
REM SpecTecinSpecTec - Compile Coq files in dependency order (Windows CMD)
setlocal
coqc syntax.v       || exit /b 1
coqc env.v          || exit /b 1
coqc primitives.v   || exit /b 1
coqc subst.v        || exit /b 1
coqc reduction_and_typing.v || exit /b 1
echo Done.
