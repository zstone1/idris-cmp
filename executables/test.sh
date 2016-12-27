#!bash/bin


cd ../CompilerFiles
idris -p effects -p lightyear -p contrib --ibcsubdir Bin --total Root.idr -o ../Testing/comp
