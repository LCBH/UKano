cat $1 | sed 's/:b/:bitstring/g' |
    sed -e 's/b,/bitstring,/g' |
    sed -e 's/ing,b)/ing,bitstring)/g' |
    sed -e 's/(b)/(bitstring)/g'    
