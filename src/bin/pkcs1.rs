/*++ @file

  Copyright ©2021-2024 Liu Yi, efikarl@yeah.net

  This program is just made available under the terms and conditions of the
  MIT license: http://www.efikarl.com/mit-license.html

  THE PROGRAM IS DISTRIBUTED UNDER THE MIT LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
--*/

use rsa::spec::pkcs1;


fn main() {
    let rsa = pkcs1::Rsa::new(512);

    println!("{:#?}", rsa);
}
