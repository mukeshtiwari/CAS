#!/bin/bash
echo "#!/bin/bash" > ./casml 
echo "$PWD/_build/extraction/casml -I $PWD/_build/src/ -I $PWD/_build/ocaml/ -I $PWD/_build/extraction/" >> ./casml 
