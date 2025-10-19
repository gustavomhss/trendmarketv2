S3EVID=out/s3_gatecheck/evidence

.PHONY: s3 s3-clean s3-orr
s3:
	bash scripts/s3/run_all_s3.sh

s3-clean:
	rm -rf out/s3_gatecheck || true

s3-orr:
	gh workflow run _mbp-s3-orr.yml || echo "Use a aba Actions se o gh não estiver configurado"
