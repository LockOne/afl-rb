#!/bin/bash
rm md5/*
../../subjects/md5sum /home/cheong/vuzzer64/fuzzer-code/datatemp/b64/* > md5/md5_1.txt
../../subjects/md5sum /home/cheong/vuzzer64/fuzzer-code/datatemp/cflow/* >> md5/md5_1.txt
../../subjects/md5sum /home/cheong/vuzzer64/fuzzer-code/datatemp/bmp2/* > md5/md5_2.txt
../../subjects/md5sum /home/cheong/vuzzer64/fuzzer-code/datatemp/mp3/* > md5/md5_3.txt
