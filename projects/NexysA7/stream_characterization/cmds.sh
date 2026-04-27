rm -f run.log
touch run.log
make bitstream >> run.log
make program >> run.log
python3 host/characterize.py --port /dev/ttyUSB1 --configs 1desc_1ch_4KB --size 4KB -v  >> run.log
