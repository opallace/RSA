#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>

#include "../bn/bn.h"

#define KEY_SIZE 512

/*	Generates an odd random number of a specified size in bits
 *
 *  Input: prime candidate size(bits), a big number pointer
 *  Output:
 * 
 */
void candidate_prime_bn(int bitlen, BIGNUM *result){
	
	BIGNUM *result_temp = init_bn();
	BIGNUM *base = int_to_bn(2);

	for(int i = 0; i < bitlen; i++){
		BIGNUM *bit;

		if(i == bitlen - 1 || i == 0){
			bit = int_to_bn(1);
		
		}else {
			bit = int_to_bn((int)(rand() % 2));
		
		}

		BIGNUM *pow  = init_bn();
		BIGNUM *exp  = int_to_bn(i);
		BIGNUM *mul  = init_bn();
		
		pow_bn(base, exp, pow);
		mul_bn(bit, pow, mul);
		sum_bn(result_temp, mul, result_temp);

		free_bn(pow);
		free_bn(exp);
		free_bn(bit);
		free_bn(mul);
	}

	copy_bn(result, result_temp);
	free_bn(result_temp);
	free_bn(base);
}

/*	Performs the primacy test of Miller Rabin in a big number
 *
 *  Input: big number candidate for prime number
 *  Output:
 * 
 */
int miller_rabin_primality_test(BIGNUM *num){

	int result = 1;

	BIGNUM *zero, *one, *two;
	zero = int_to_bn(0);
	one  = int_to_bn(1);
	two  = int_to_bn(2);
	
	BIGNUM *s = int_to_bn(0);
	BIGNUM *x = init_bn();
	BIGNUM *a = init_bn();
	BIGNUM *r = init_bn();
	BIGNUM *j = init_bn();
		
	sub_bn(num, one, r);
	
	BIGNUM *mod = init_bn();
	mod_bn(r, two, mod);

	while(comp_bn(mod, zero) == 0){
		sum_bn(s, one, s);
		div_bn(r, two, r);

		mod_bn(r, two, mod);
	}

	for(int i = 0; i < 1; i++){
		BIGNUM *su = init_bn();
		sub_bn(num, one, su);

		random_range_bn(two, su, a);
		pow_mod_bn(a, r, num, x);
		
		BIGNUM *sub = init_bn();
		sub_bn(num, one, sub);

		if(comp_bn(x, one) != 0 && comp_bn(x, sub) != 0){
			
			BIGNUM *sub2 = init_bn();
			sub_bn(s, one, sub2);

			for(BIGNUM *j = int_to_bn(0); comp_bn(j, sub2) == -1; sum_bn(j, one, j)){
				pow_mod_bn(x, two, num, x);

				if(comp_bn(x, one) == 0){
           			result = 0;
					break;
				}
				
				BIGNUM *sub3 = init_bn();
				sub_bn(num, one, sub3);

				if(comp_bn(x, sub3) == 0){
					break;
				}

				sub_bn(s, one, sub2);
				free_bn(sub3);
			}
			
			BIGNUM *sub4 = init_bn();
			sub_bn(num, one, sub4);

			if(comp_bn(x, sub4) != 0){
				result = 0;
				break;
			}

			free_bn(sub2);
			free_bn(sub4);
		}

		free_bn(su);
		free_bn(sub);
	}
	
	free_bn(zero);
	free_bn(one);
	free_bn(two);
	free_bn(s);
	free_bn(x);
	free_bn(a);
	free_bn(r);
	free_bn(j);
	free_bn(mod);

	return result;
}

void write_key_file(const char *nk, BIGNUM *key, FILE *file){
	fprintf(file, "%s: ", nk);
	for(int i = 0; i < key->size; i++){
		fprintf(file, "%i", key->digits[i]);
	}
	fprintf(file, "\n");
}

void read_key_file(BIGNUM *key, FILE *file){
	char buffer[1000];
	fgets(buffer, 1000, file);

	for(int i = 3; buffer[i] != '\0' && buffer[i] != '\n'; i++){
		key->digits = realloc(key->digits, ++key->size * sizeof(uint8_t));
		key->digits[key->size - 1] = buffer[i] - 48;
	}
}

/*	Generates a prime number
 *
 *  Input: prime number size in bits
 *  Output: a big number pointer
 * 
 */
BIGNUM* generate_prime(int size){

	BIGNUM *prime = init_bn();
	
	do{
		candidate_prime_bn(size, prime);

	}while(!miller_rabin_primality_test(prime));

	return prime;
}

/*	Calculates the size of a file
 *
 *  Input: a file pointer
 *  Output: file size
 * 
 */
int getSizeFile(FILE *file){
	fseek(file, 0, SEEK_END);
	int size = ftell(file);
	fseek(file, 0, SEEK_SET);

	return size;
}

/*	Generates RSA keys and creates public and private key files
 *
 *  Input:
 *  Output:
 * 
 */
void generate_keys(){
	srand(time(NULL));

	BIGNUM *one = int_to_bn(1);
	BIGNUM *two = int_to_bn(2);

	BIGNUM *p   = init_bn();
	BIGNUM *q   = init_bn();
	BIGNUM *n   = init_bn();
	BIGNUM *phi = init_bn();
	BIGNUM *e   = init_bn();
	BIGNUM *d   = init_bn();

	copy_bn(p, generate_prime(KEY_SIZE / 2));
	copy_bn(q, generate_prime(KEY_SIZE / 2));

	mul_bn(p, q, n);

	BIGNUM *sub  = init_bn();
	BIGNUM *sub1 = init_bn();

	sub_bn(p, one, sub);
	sub_bn(q, one, sub1);
	mul_bn(sub, sub1, phi);
	
	BIGNUM *mdc = init_bn();
	BIGNUM *sub2 = init_bn();

	do{

		sub_bn(phi, one, sub2);
		random_range_bn(two, sub2, e);
		mdc_bn(e, phi, mdc);

	}while(comp_bn(mdc, one) != 0);
	
	mod_inverse_bn(e, phi, d);

	FILE *public  = fopen("public.key", "w+");
	FILE *private = fopen("private.key", "w+");

	write_key_file("D", d, private);
	write_key_file("P", p, private);
	write_key_file("Q", q, private);

	write_key_file("N", n, public);
	write_key_file("E", e, public);
	
	free_bn(one);
	free_bn(two);
	free_bn(p);
	free_bn(q);
	free_bn(n);
	free_bn(phi);
	free_bn(e);
	free_bn(d);
	free_bn(sub);
	free_bn(sub1);
	free_bn(mdc);

	fclose(public);
	fclose(private);
}

/*	Transforms a string of octets into a big number
 *
 *  Input: a string of octets, a big number
 *  Output:
 * 
 */
void OS2IP(BIGNUM *data, BIGNUM *primitive){
	BIGNUM *base = int_to_bn(256);
	BIGNUM *result = int_to_bn(0);

	for (int i = 0; i < data->size; ++i){
		BIGNUM *data_bn = int_to_bn(data->digits[i]);
		BIGNUM *expoent = int_to_bn((data->size - 1) - i);

		BIGNUM *pow = init_bn();
		pow_bn(base, expoent, pow);

		BIGNUM *mul = init_bn();
		mul_bn(data_bn, pow, mul);

		sum_bn(result, mul, result);

		free_bn(data_bn);
		free_bn(expoent);
		free_bn(pow);
		free_bn(mul);
	}

	copy_bn(primitive, result);
	free_bn(base);
	free_bn(result);
}

/*	Transform a big number into an octet string
 *
 *  Input: two big numbers
 *  Output:
 * 
 */
void I2OSP(BIGNUM *ddata, BIGNUM *primitive){
	BIGNUM *zero = int_to_bn(0);
	BIGNUM *base = int_to_bn(256);
	
	BIGNUM *pow  = init_bn();
	BIGNUM *xLen = int_to_bn(KEY_SIZE/8);
	pow_bn(base, xLen, pow);

	if(comp_bn(ddata, pow) == 1){
		printf("ERROR!\n");

	}else {

		int size_temp = 0;
		BIGNUM *data = init_bn();
		copy_bn(data, ddata);

		while(comp_bn(data, zero) != 0){
			BIGNUM *mod = init_bn();
			mod_bn(data, base, mod);

			primitive->digits[size_temp++] = bn_to_int(mod);

			div_bn(data, base, data);
		}

		rev_bn(primitive);
	}
}

/*	Encrypts a big number using the keys e and n
 *
 *  Input: key e, key n, big number to be encrypted, big number that will store the result
 *  Output:
 * 
 */
void RSAEP(BIGNUM *e, BIGNUM *n, BIGNUM *m, BIGNUM *c){
	BIGNUM *result = init_bn();
	pow_mod_bn(m, e, n, result);

	copy_bn(c, result);
	free_bn(result);
}

/*	Decrypts a big number using the keys d and n
 *
 *  Input: key n, key d, big number to be decrypted, big number that will store the result
 *  Output:
 * 
 */
void RSADP(BIGNUM *n, BIGNUM *d, BIGNUM *c, BIGNUM *m){
	BIGNUM *result = init_bn();
	pow_mod_bn(c, d, n, result);

	copy_bn(m, result);
	free_bn(result);
}


/*	Encodes a string of octets in the format defined by RFC 2313
 *
 *  Input: key n, a string of octets in big number format, big number that will store the result
 *  Output:
 * 
 *	Format: EB = 00 || BT || PS || 00 || D.
 *
 *			BT identifies the structure of the coding block
 *			PS is a pad of randomly generated nonzero octets
 *			D  are the octets to be encoded
 */
void encode_block_formatting(BIGNUM *n, BIGNUM *data, BIGNUM *EB){
	srand(time(NULL));

	BIGNUM *EB_temp = init_bn();
	EB_temp->digits = malloc(KEY_SIZE/8);
	EB_temp->size   = KEY_SIZE/8;

	EB_temp->digits[0] = 0x00;
	EB_temp->digits[1] = 0x02;

	int i = 2;
	for (; i < ((EB_temp->size - 3) - data->size) + 2; ++i){
		EB_temp->digits[i] = rand() % 0xFF + 1;
	}

	EB_temp->digits[i++] = 0x00;

	for (int j = 0; i < EB_temp->size; ++i, ++j){
		EB_temp->digits[i] = data->digits[j];
	}

	copy_bn(EB, EB_temp);
	free_bn(EB_temp);
}

/*	Decodes a block of octets encoded in rfc 2313 format
 *
 *  Input: key n, formatted block(big number), big number that will store the result
 *  Output:
 * 
 *	Format: EB = 00 || BT || PS || 00 || D.
 *
 *			BT identifies the structure of the coding block
 *			PS is a pad of randomly generated nonzero octets
 *			D  are the octets to be encoded
 */
void decode_block_formatting(BIGNUM *n, BIGNUM *EB, BIGNUM *data){
	BIGNUM *data_temp = init_bn();
	
	int i = 2;
	for (; EB->digits[i] != 0x00; ++i);

	for (i += 1; i < EB->size; ++i){
		data_temp->digits = realloc(data_temp->digits, ++data_temp->size);
		data_temp->digits[data_temp->size - 1] = EB->digits[i];
	}

	copy_bn(data, data_temp);
	free_bn(data_temp);
}

/*	Encrypts a file in RSA
 *
 *  Input:
 *  Output:
 */
void encrypt_file(){
	char filename[30];
	printf("\n   filename: ");
	scanf("%s", &filename);

	FILE *public = fopen("public.key", "r");
	FILE *in     = fopen(filename, "rb");
	FILE *out    = fopen("encrypted", "w+b");

	BIGNUM *n = init_bn();
	BIGNUM *e = init_bn();
	BIGNUM *primitive = init_bn();

	read_key_file(n, public);
	read_key_file(e, public);

	BIGNUM *data_out = init_bn();
	BIGNUM *data_in  = init_bn();
	data_in->size    = getSizeFile(in);
	data_in->digits  = malloc(data_in->size);

	fread(data_in->digits, 1, data_in->size, in);
	
	BIGNUM *EB = init_bn();
	encode_block_formatting(n, data_in, EB);

	OS2IP(EB, primitive);
	RSAEP(e, n, primitive, data_out);

	fwrite(data_out->digits, 1, data_out->size, out);

	free_bn(e);
	free_bn(n);
	
	fclose(public);
	fclose(in);
}

/*	Decrypts an RSA encrypted file
 *
 *  Input:
 *  Output:
 */
void decrypt_file(){
	char filename[30];
	printf("\n    filename: ");
	scanf("%s", &filename);
	
	FILE *private = fopen("private.key", "r");
	FILE *public  = fopen("public.key", "r");
	FILE *in      = fopen(filename, "rb");
	FILE *out     = fopen("decrypted", "w+b");

	BIGNUM *p = init_bn();
	BIGNUM *q = init_bn();
	BIGNUM *d = init_bn();
	BIGNUM *n = init_bn();

	read_key_file(n, public);
	read_key_file(d, private);

	BIGNUM *primitive = init_bn();
	BIGNUM *data_out = init_bn();
	BIGNUM *data_in  = init_bn();
	data_in->size    = getSizeFile(in);
	data_in->digits  = malloc(data_in->size);

	fread(data_in->digits, 1, data_in->size, in);

	BIGNUM *EB = init_bn();
	EB->digits = malloc(KEY_SIZE/8);
	EB->size   = KEY_SIZE/8;

	RSADP(n, d, data_in, primitive);
	I2OSP(primitive, EB);

	decode_block_formatting(n, EB, data_out);
	
	fwrite(data_out->digits, 1, data_out->size, out);

	free_bn(d);
	free_bn(n);

	fclose(out);
	fclose(private);
	fclose(public);
	fclose(in);
}

int main(){

	srand(time(NULL));

	printf("   ========================================================\n");
	printf("   =                                                      =\n");
	printf("   =                                                      =\n");
	printf("   =                                                      =\n");
	printf("   =                   RSA CALCULATOR                     =\n");
	printf("   =                                                      =\n");
	printf("   =                                                      =\n");
	printf("   =                                                      =\n");
	printf("   ========================================================\n\n");
	
	printf("   (1) Generate Keys\n");
	printf("   (2) Encrypt File\n");
	printf("   (3) Decrypt File\n\n");
	
	printf("   > ");
	
	int option;
	scanf("%i", &option);
	
	switch(option){
		case 1:
			generate_keys();
			break;

		case 2:
			encrypt_file();
			break;

		case 3:
		    decrypt_file();	
			break;

		default:
			printf("error!\n");
	}

	return 0;
}
