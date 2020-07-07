#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "../bn/bn.h"

#define KEY_SIZE 1024

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

int is_prime(BIGNUM *num){

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

BIGNUM* generate_prime(){

	BIGNUM *prime = init_bn();
	
	do{
		candidate_prime_bn(KEY_SIZE / 2, prime);
		println_bn(prime);

	}while(!is_prime(prime));

	return prime;
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
		key->digits = realloc(key->digits, ++key->size * sizeof(int));
		key->digits[key->size - 1] = buffer[i] - 48;
	}
}

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

	copy_bn(p, generate_prime());
	copy_bn(q, generate_prime());

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

	write_key_file("P", p, private);
	write_key_file("Q", q, private);
	write_key_file("D", d, private);
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

void encrypt_file(){
	char filename[30];
	printf("\n   filename: ");
	scanf("%s", &filename);

	FILE *public = fopen("public.key", "r");
	FILE *file   = fopen(filename, "rb");

	BIGNUM *n = init_bn();
	BIGNUM *e = init_bn();
	
	read_key_file(n, public);
	read_key_file(e, public);
	
	FILE *out = fopen("enc.txt", "w+");
	int c;
	while((c = fgetc(file)) != EOF){
		BIGNUM *cc = int_to_bn(c);

		BIGNUM *pow = init_bn();
		pow_mod_bn(cc, e, n, pow);

		print_bn_file(out, pow);
		fprintf(out, "\n");

		free_bn(pow);
		free_bn(cc);
	}

	free_bn(e);
	free_bn(n);
	
	fclose(public);
	fclose(file);
}


void decrypt_file(){
	char filename[30];
	printf("\n    filename: ");
	scanf("%s", &filename);
	
	FILE *private = fopen("private.key", "r");
	FILE *public  = fopen("public.key", "r");
	FILE *file    = fopen(filename, "rb");


	BIGNUM *p = init_bn();
	BIGNUM *q = init_bn();
	BIGNUM *d = init_bn();
	BIGNUM *n = init_bn();

	read_key_file(n, public);

	read_key_file(p, private);
	read_key_file(q, private);
	read_key_file(d, private);
	
	FILE *out = fopen("msg.txt", "w+");
	
	BIGNUM *cc = init_bn();
	int c;
	while((c = fgetc(file)) != EOF){
		if(c == '\n'){
			
			BIGNUM *pow = init_bn();
			pow_mod_bn(cc, d, n, pow);

			fputc(bn_to_int(pow), out);

			free(cc->digits);
			cc->digits = NULL;
			cc->size = 0;

			free_bn(pow);

		}else {
			cc->digits = realloc(cc->digits, ++cc->size * sizeof(int));
			cc->digits[cc->size - 1] = c - 48;
		}
	}

	free_bn(d);
	free_bn(n);
	free_bn(cc);

	fclose(out);
	fclose(private);
	fclose(public);
	fclose(file);
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
	
	int opt;
	scanf("%i", &opt);
	
	switch(opt){
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
