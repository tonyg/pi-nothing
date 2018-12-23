(* ocamlopt unix.cmxa mandelbrot.ml *)

let putrgb buf stride x y r g b =
  let i = 3 * (x + (y * stride)) in
  String.set buf i r;
  String.set buf (i+1) g;
  String.set buf (i+2) b;
  ()

let escape_iteration_count cx cy =
  let iteration_limit = 256 in
  let rec loop i zx zy =
    if i >= iteration_limit
    then -1
    else let zx2 = zx *. zx in
	 let zy2 = zy *. zy in
	 if (zx2 +. zy2) >= 4.0
	 then i
	 else let tx = cx +. (zx2 -. zy2) in
	      let ty = cy +. (2.0 *. zx *. zy) in
	      loop (i + 1) tx ty
  in loop 0 0.0 0.0

let main () =
  let width = 1024 in
  let height = 1024 in
  Printf.printf "P6 %d %d 255\n%!" width height;
  let buf = String.create (width * height * 3) in
  let rec yloop y =
    if y >= height
    then ()
    else let rec xloop x =
	   if x >= width
	   then yloop (y + 1)
	   else let i =
		  escape_iteration_count
		    (-2.0 +. ((float_of_int x) *. (4.0 /. (float_of_int width))))
		    (-2.0 +. ((float_of_int y) *. (4.0 /. (float_of_int height))))
		in
		let b = char_of_int (if i == -1 then 0 else i) in
		putrgb buf width x y b b b;
		xloop (x + 1)
	 in xloop 0
  in
  yloop 0;
  let _ = Unix.write Unix.stdout buf 0 (String.length buf) in
  ()

let _ = main ()
