import sys
import subprocess as sub
import string

seahorn_path = sys.argv[1]
pred_num = sys.argv[2]
benchmark_path = sys.argv[3]

dic_path = seahorn_path + '/experiment/pred_dictionary'

fout_path = seahorn_path + '/experiment/preds_temp'
result_dir = seahorn_path + '/experiment/result'
err_dir = seahorn_path + '/experiment/err'

i = 1
while i<= string.atoi(pred_num) :
  j = 1
  dic = open(dic_path, 'r')
  fout = open(fout_path, 'w')
  while j<=i :
    line = dic.readline()
    fout.write(line)
    j += 1
  fout.close()
  #print 'FILE CONTENT:'
  #fin = open(fout_path, 'r')
  #print fin.read()
  # run seahorn
  res_out = result_dir + '/' + str(i) + '.res'
  res_err = err_dir + '/' + str(i) + '.err'
  p = sub.Popen([seahorn_path + '/build/run/bin/sea', '--mem=-1', '-m64', 'pf', '--step=large', '-g', '--horn-global-constraints=true', '--track=mem', '--horn-stats', '--enable-nondet-init', '--strip-extern', '--externalize-addr-taken-functions', '--horn-singleton-aliases=true', '--devirt-functions', '--horn-ignore-calloc=false', '--enable-indvar', '--enable-loop-idiom', '--horn-make-undef-warning-error=false', '--inline', benchmark_path, '--horn-pred-abs'], stdout=open(res_out, 'w'), stderr=open(res_err, 'w'))
  p.wait()
  i += 1
