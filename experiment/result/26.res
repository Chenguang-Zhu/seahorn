/usr/bin/clang-3.6 -c -emit-llvm -D__SEAHORN__ -fgnu89-inline -m64 -g -I/home/chenguang/Desktop/seahorn/build/run/include -o /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.bc /home/chenguang/Desktop/PABS-experiment/case5/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.c
/home/chenguang/Desktop/seahorn/build/run/bin/seapp -o /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.bc --horn-inline-all --strip-extern=true --devirt-functions --externalize-addr-taken-funcs --kill-vaarg=true /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.bc
/home/chenguang/Desktop/seahorn/build/run/bin/seapp -o /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.ms.bc --horn-mixed-sem --ms-reduce-main /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.bc
/home/chenguang/Desktop/seahorn/build/run/bin/seaopt -f -funit-at-a-time -o /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.ms.o.bc -O3 /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.ms.bc
/home/chenguang/Desktop/seahorn/build/run/bin/seahorn --keep-shadows=true --horn-solve -horn-inter-proc -horn-sem-lvl=mem --horn-step=large /tmp/sea-E3Od4F/linux-3.8-rc1-32_7a-drivers--net--dsa--mv88e6xxx_drv.ko-ldv_main2_true-unreach-call.cil.out.pp.ms.o.bc --horn-global-constraints=true --horn-stats --horn-singleton-aliases=true --horn-ignore-calloc=false --horn-make-undef-warning-error=false --horn-pred-abs
unsat


************** BRUNCH STATS ***************** 
BRUNCH_STAT HornClauseDB::loadZFixedPoint 1.34
BRUNCH_STAT HornifyModule 4.17
BRUNCH_STAT LargeHornifyFunction 3.87
BRUNCH_STAT Pabs solve 133.76
BRUNCH_STAT seahorn_total 139.10
************** BRUNCH STATS END ***************** 
