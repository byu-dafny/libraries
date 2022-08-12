baseDir=$PWD
cd src
pkill -9 -f "z3/bin/z3"
pkill -9 -f "local/bin/z3"
for filename in $(find . -name '*.dfy'); do
    [ -e "$filename" ] || continue
    # create equivalent directories in test and stats folders:
    filename=${filename:2}
    if [ "$filename" = "AllSource.dfy" ]; then
        continue
    fi
    dirname=""
    if [[ $filename == *"/"* ]]; then
        dirname=${filename%/*}
        cd ../stats/
        mkdir -p $dirname
        cd ../test/
        mkdir -p $dirname
        cd ../src/
    fi
    cd ../test/
    # check if we have already generated a test for this file
    if [ -e "$filename" ]; then
        echo "Already generated tests for "$filename
        cd ../src
        continue
    fi
    echo $filename
    jsonname=${filename%.*}.json
    if [[ ! -z $dirname ]]; then
        cd $dirname
    fi
    relative="../"
    while [[ $dirname == *"/"* ]]; do
        dirname=${dirname%/*}
        relative=$relative../
    done
    if [[ ! -z $dirname ]]; then
        relative=$relative../
    fi
    dotnet $baseDir/dafny/Binaries/Dafny.dll /definiteAssignment:3 /warnShadowing /timeLimit:5 /generateTestMode:Block /generateTestOracle:Spec /generateTestSeqLengthLimit:100 /generateTestVerbose /generateTestPrintStats:$baseDir/stats/$jsonname $relative/src/$filename > ${filename##*/}
    # kill all z3 processes that might still be running
    pkill -9 -f "z3/bin/z3"
    pkill -9 -f "local/bin/z3"
    cd - > /dev/null
    cd ../src
done