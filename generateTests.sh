for filename in $(find src/ -name '*.dfy'); do
    [ -e "$filename" ] || continue
    propername=${filename##*/}
    cd tests/
    dotnet ../dafny/Binaries/Dafny.dll /definiteAssignment:3 /warnShadowing /generateTestTimeout:5 /generateTestMode:Block /generateTestSeqLengthLimit:5 ../$filename > $propername
    cd ../
done
