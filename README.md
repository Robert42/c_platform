THE SOFTWARE IS PROVIDED "AS IS"  AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.

## Formal Verification

While I am verifying some properties of the application, I make no claims of
the software being bugfree:
- Many important proprties arent' verified.
- There may be a mistakes in the specification.
- There may be a bugs in the verification process/system.

To reduce the vurden of verification, I've taken some shortcuts:
- Failing runtime assertions can at any time unexpectedly exit the application.
  I am using ACSL's `admit` keyword to hide this behavior from the verification
  system.

This behavior would be inacceptable in a critical software system.
But for the kind of software I have in mind, crashing is preferable over
generating incorrect output data.
So I hide the unexpected exit from the verification system to reduce the burden
of verifying the software so I can verify some actually relevant properties.

