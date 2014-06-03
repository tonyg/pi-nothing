(* ocamlopt unix.cmxa mandelbrot.ml *)

open Int64

let int_to_fix i = shift_left (of_int i) 16

let buf = String.create 3
let putrgb r g b =
  String.set buf 0 r;
  String.set buf 1 g;
  String.set buf 2 b;
  let _ = Unix.write Unix.stdout buf 0 3 in ()

let escape_iteration_count cx cy =
  let iteration_limit = 256 in
  let rec loop i zx zy =
    if i >= iteration_limit
    then -1
    else let zx2 = shift_right (mul zx zx) 16 in
	 let zy2 = shift_right (mul zy zy) 16 in
	 if compare (add zx2 zy2) (int_to_fix 4) >= 0
	 then i
	 else let tx = add cx (sub zx2 zy2) in
	      let ty = add cy (shift_right (mul zx zy) 15) in
	      loop (i + 1) tx ty
  in loop 0 zero zero

let main () =
  let width = 1024 in
  let height = 1024 in
  Printf.printf "P6 %d %d 255\n%!" width height;
  let rec yloop y =
    if y >= height
    then ()
    else let rec xloop x =
	   if x >= width
	   then yloop (y + 1)
	   else let i =
		  escape_iteration_count
		    (add (int_to_fix (-2)) (mul (of_int x) (div (int_to_fix 4) (of_int width))))
		    (add (int_to_fix (-2)) (mul (of_int y) (div (int_to_fix 4) (of_int height))))
		in
		let b = char_of_int (if i == -1 then 0 else i) in
		putrgb b b b;
		xloop (x + 1)
	 in xloop 0
  in yloop 0

let _ = main ()
