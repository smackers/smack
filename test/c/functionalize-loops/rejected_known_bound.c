// @expect verified
// @checkbpl awk '/lambda/ { found = 1 } END { exit found }'
// @checkout grep -F "main: --unroll=6 is needed to explore it fully"

int main(void) {
  volatile unsigned value = 0;
  for (unsigned i = 0; i < 5; ++i)
    value = i;
  return 0;
}
