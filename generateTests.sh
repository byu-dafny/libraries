for filename in $(find src/ -name '*.dfy'); do
    [ -e "$filename" ] || continue
    propername=${filename##*/}
    if [ "$propername" = "AllSource.dfy" ]; then
        continue
    fi
    echo "Generating tests for $propername"
    cd tests/
    dotnet ../dafny/Binaries/Dafny.dll /definiteAssignment:3 /warnShadowing /generateTestTimeout:5 /generateTestMode:Block /generateTestSeqLengthLimit:8 ../$filename > $propername
    pkill -9 -f "z3/bin/z3"
    pkill -9 -f "usr/local/bin/z3"
    cd ../
done
