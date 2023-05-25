__kernel void do_duplicate_check(  __global uchar*  buffer,
	                               __global uchar*  last,
	                               __global uchar*  result) {
	int x = get_global_id(0); // Width * Pixel Length
	int y = get_global_id(1); // Height
	int z = get_global_id(2); // Face
	
	int stride = get_global_size(0);
	int height = get_global_size(1);

	int index = (z * stride * height) + (y * stride) + x;

	// Get the Original and Last Values to Compare
	uchar orig = buffer[index];
	uchar comp = last[index];

	// Assign the Original to the Last
	last[index] = orig;

	if (orig != comp) {
		result[0] = 1;
	}


	//uchar zero = 0;

	//if (orig != comp) {
	//	atomic_compare_exchange_strong(&result[0], &zero, 1);
	//}

	//uchar old_value = atomic_load(&result[0]);
    //if (old_value == 0) {
    //    uchar new_value = 1;
    //    atomic_compare_exchange_strong(&result[0], &old_value, new_value);
    //}
}
