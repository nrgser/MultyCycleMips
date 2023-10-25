lui $t1,0xffff
sw  $t1,200($zero)
sll $t2,$t1,4
sw $t2,204($zero)
addi $t3,$zero,4
sllv $t4,$t1,$t3
sw $t4,208($zero)