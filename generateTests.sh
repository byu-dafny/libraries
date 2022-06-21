for filename in $(find src/ -name '*.dfy'); do
    [ -e "$filename" ] || continue
    propername=${filename##*/}
    if [ "$propername" = "AllSource.dfy" ]; then
        continue
    fi
    cd tests/
    dotnet ../dafny/Binaries/Dafny.dll /definiteAssignment:3 /warnShadowing /generateTestTimeout:5 /generateTestMode:Block /generateTestSeqLengthLimit:5 ../$filename > $propername
    cd ../
done
