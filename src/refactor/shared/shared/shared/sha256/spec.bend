import Base
import ../shared/shared.bend as Shared

# SHA-256 (FIPS 180-4) of words, each word read as four bytes, most significant
# byte first. Its result is what the standard says, so a test against the
# standard's own vectors checks it, not a law. Nobody can find two lists of
# words with one SHA-256: that is assumed, not proven (Trust 1).

# the SHA-256 of the words ws, as 8 words
law Sha256.of_words:
  for ws: List<&2, U32>
  Shared.Row(U32, 8n)
