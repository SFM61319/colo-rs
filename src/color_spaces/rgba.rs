//! An 8-bit RGBA color.
//!
//! This module contains the [`Rgba`] color space type, and several error types
//! that may result from working with [`Rgba`] colors.
//!
//! # Examples
//!
//! You can create a new [`Rgba`] color from individual channels:
//!
//! ```
//! let red = colo_rs::Rgba::new(255, 0, 0, 255);
//! let green = colo_rs::Rgba::from([0, 255, 0]);
//! let blue = colo_rs::Rgba::from([0, 0, 255, 255]);
//! let black = colo_rs::Rgba::from((0, 0, 0));
//! let white = colo_rs::Rgba::from((255, 255, 255, 255));
//! let translucent_gray = colo_rs::Rgba::from(0x80_80_80_80);
//! ```
//!
//! Or use the default transparent black color:
//!
//! ```
//! let transparent = colo_rs::Rgba::default();
//! ```
//!
//! Check if an [`Rgba`] color is transparent or not:
//!
//! ```
//! let red = colo_rs::Rgba::new(255, 0, 0, 255);
//! let green = colo_rs::Rgba::new(0, 255, 0, 255);
//! let blue = colo_rs::Rgba::new(0, 0, 255, 255);
//! let black = colo_rs::Rgba::new(0, 0, 0, 255);
//! let white = colo_rs::Rgba::new(255, 255, 255, 255);
//! let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
//! let transparent = colo_rs::Rgba::default();
//!
//! assert!(!red.is_transparent());
//! assert!(!green.is_transparent());
//! assert!(!blue.is_transparent());
//! assert!(!black.is_transparent());
//! assert!(!white.is_transparent());
//! assert!(!translucent_gray.is_transparent());
//! assert!(transparent.is_transparent());
//! ```
//!
//! Check if an [`Rgba`] color is translucent or not:
//!
//! ```
//! let red = colo_rs::Rgba::new(255, 0, 0, 255);
//! let green = colo_rs::Rgba::new(0, 255, 0, 255);
//! let blue = colo_rs::Rgba::new(0, 0, 255, 255);
//! let black = colo_rs::Rgba::new(0, 0, 0, 255);
//! let white = colo_rs::Rgba::new(255, 255, 255, 255);
//! let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
//! let transparent = colo_rs::Rgba::default();
//!
//! assert!(!red.is_translucent());
//! assert!(!green.is_translucent());
//! assert!(!blue.is_translucent());
//! assert!(!black.is_translucent());
//! assert!(!white.is_translucent());
//! assert!(translucent_gray.is_translucent());
//! assert!(!transparent.is_translucent());
//! ```
//!
//! Check if an [`Rgba`] color is opaque or not:
//!
//! ```
//! let red = colo_rs::Rgba::new(255, 0, 0, 255);
//! let green = colo_rs::Rgba::new(0, 255, 0, 255);
//! let blue = colo_rs::Rgba::new(0, 0, 255, 255);
//! let black = colo_rs::Rgba::new(0, 0, 0, 255);
//! let white = colo_rs::Rgba::new(255, 255, 255, 255);
//! let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
//! let transparent = colo_rs::Rgba::default();
//!
//! assert!(red.is_opaque());
//! assert!(green.is_opaque());
//! assert!(blue.is_opaque());
//! assert!(black.is_opaque());
//! assert!(white.is_opaque());
//! assert!(!translucent_gray.is_opaque());
//! assert!(!transparent.is_opaque());
//! ```

use std::{
    fmt::{Display, Formatter},
    ops::RangeInclusive,
};

/// An 8-bit RGBA color.
///
/// The `Rgba` color space is the most commonly used color space in which the
/// red, green, blue, and alpha channels are all 8-bit values. It has a close
/// relationship with it's hexadecimal counterpart, the hex color (#RRGGBBAA).
///
/// The normalized representation of red, green, blue, and alpha values must be
/// in the range \[0.0, 1.0\].
///
/// # Examples
///
/// You can create a new `Rgba` color from individual channels:
///
/// ```
/// let red = colo_rs::Rgba::new(255, 0, 0, 255);
/// let green = colo_rs::Rgba::from([0, 255, 0]);
/// let blue = colo_rs::Rgba::from([0, 0, 255, 255]);
/// let black = colo_rs::Rgba::from((0, 0, 0));
/// let white = colo_rs::Rgba::from((255, 255, 255, 255));
/// let translucent_gray = colo_rs::Rgba::from(0x80_80_80_80);
/// let transparent = colo_rs::Rgba::new(0, 0, 0, 0);
/// ```
///
/// Or use the default transparent black color:
///
/// ```
/// let transparent = colo_rs::Rgba::default();
/// ```
///
/// Check if an `Rgba` color is transparent or not:
///
/// ```
/// let red = colo_rs::Rgba::new(255, 0, 0, 255);
/// let green = colo_rs::Rgba::new(0, 255, 0, 255);
/// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
/// let black = colo_rs::Rgba::new(0, 0, 0, 255);
/// let white = colo_rs::Rgba::new(255, 255, 255, 255);
/// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
/// let transparent = colo_rs::Rgba::default();
///
/// assert!(!red.is_transparent());
/// assert!(!green.is_transparent());
/// assert!(!blue.is_transparent());
/// assert!(!black.is_transparent());
/// assert!(!white.is_transparent());
/// assert!(!translucent_gray.is_transparent());
/// assert!(transparent.is_transparent());
/// ```
///
/// Check if an `Rgba` color is translucent or not:
///
/// ```
/// let red = colo_rs::Rgba::new(255, 0, 0, 255);
/// let green = colo_rs::Rgba::new(0, 255, 0, 255);
/// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
/// let black = colo_rs::Rgba::new(0, 0, 0, 255);
/// let white = colo_rs::Rgba::new(255, 255, 255, 255);
/// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
/// let transparent = colo_rs::Rgba::default();
///
/// assert!(!red.is_translucent());
/// assert!(!green.is_translucent());
/// assert!(!blue.is_translucent());
/// assert!(!black.is_translucent());
/// assert!(!white.is_translucent());
/// assert!(translucent_gray.is_translucent());
/// assert!(!transparent.is_translucent());
/// ```
///
/// Check if an `Rgba` color is opaque or not:
///
/// ```
/// let red = colo_rs::Rgba::new(255, 0, 0, 255);
/// let green = colo_rs::Rgba::new(0, 255, 0, 255);
/// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
/// let black = colo_rs::Rgba::new(0, 0, 0, 255);
/// let white = colo_rs::Rgba::new(255, 255, 255, 255);
/// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
/// let transparent = colo_rs::Rgba::default();
///
/// assert!(red.is_opaque());
/// assert!(green.is_opaque());
/// assert!(blue.is_opaque());
/// assert!(black.is_opaque());
/// assert!(white.is_opaque());
/// assert!(!translucent_gray.is_opaque());
/// assert!(!transparent.is_opaque());
/// ```
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct Rgba {
    /// The red channel.
    r: u8,

    /// The green channel.
    g: u8,

    /// The blue channel.
    b: u8,

    /// The alpha channel.
    a: u8,
}

impl Rgba {
    /// The minimum value for each channel.
    pub const CHANNEL_MIN: u8 = u8::MIN;

    /// The maximum value for each channel.
    pub const CHANNEL_MAX: u8 = u8::MAX;

    /// The range of each channel.
    pub const CHANNEL_RANGE: RangeInclusive<u8> = Self::CHANNEL_MIN..=Self::CHANNEL_MAX;

    /// The minimum normalized value for each channel.
    pub const NORM_CHANNEL_MIN: f64 = 0.0f64;

    /// The maximum normalized value for each channel.
    pub const NORM_CHANNEL_MAX: f64 = 1.0f64;

    /// The range of each normalized channel.
    pub const NORM_CHANNEL_RANGE: RangeInclusive<f64> =
        Self::NORM_CHANNEL_MIN..=Self::NORM_CHANNEL_MAX;

    /// Creates a new `Rgba` color with the given r, g, b, and a channel values.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::new(255, 0, 0, 255);
    /// let green = colo_rs::Rgba::new(0, 255, 0, 255);
    /// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
    /// let black = colo_rs::Rgba::new(0, 0, 0, 255);
    /// let white = colo_rs::Rgba::new(255, 255, 255, 255);
    /// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
    /// let transparent = colo_rs::Rgba::new(0, 0, 0, 0);
    /// ```
    #[inline]
    pub const fn new(r: u8, g: u8, b: u8, a: u8) -> Self {
        Self { r, g, b, a }
    }

    /// Gets the red channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::new(255, 0, 0, 255);
    /// assert_eq!(red.r(), 255);
    /// ```
    #[inline]
    pub const fn r(&self) -> u8 {
        self.r
    }

    /// Sets the red channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Rgba::new(128, 0, 0, 255);
    /// red.set_r(255);
    /// assert_eq!(red.r(), 255);
    /// ```
    #[inline]
    pub fn set_r(&mut self, value: u8) {
        self.r = value;
    }

    /// Gets the normalized red channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::from((1.0, 0.0, 0.0, 1.0));
    /// assert_eq!(red.r_norm(), 1.0);
    /// ```
    #[inline]
    pub fn r_norm(&self) -> f64 {
        Self::normalize(self.r())
    }

    /// Sets the normalized red channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut red = colo_rs::Rgba::from((0.5, 0.0, 0.0, 1.0));
    /// red.set_r_norm(1.0);
    /// assert_eq!(red.r_norm(), 1.0);
    /// ```
    #[inline]
    pub fn set_r_norm(&mut self, value: f64) {
        self.set_r(Self::denormalize(value));
    }

    /// Gets the green channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let green = colo_rs::Rgba::new(0, 255, 0, 255);
    /// assert_eq!(green.g(), 255);
    /// ```
    #[inline]
    pub const fn g(&self) -> u8 {
        self.g
    }

    /// Sets the green channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut green = colo_rs::Rgba::new(0, 128, 0, 255);
    /// green.set_g(255);
    /// assert_eq!(green.g(), 255);
    /// ```
    #[inline]
    pub fn set_g(&mut self, value: u8) {
        self.g = value;
    }

    /// Gets the normalized green channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let green = colo_rs::Rgba::from((0.0, 1.0, 0.0, 1.0));
    /// assert_eq!(green.g_norm(), 1.0);
    /// ```
    #[inline]
    pub fn g_norm(&self) -> f64 {
        Self::normalize(self.g())
    }

    /// Sets the normalized green channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut green = colo_rs::Rgba::from((0.0, 0.5, 0.0, 1.0));
    /// green.set_g_norm(1.0);
    /// assert_eq!(green.g_norm(), 1.0);
    /// ```
    #[inline]
    pub fn set_g_norm(&mut self, value: f64) {
        self.set_g(Self::denormalize(value));
    }

    /// Gets the blue channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
    /// assert_eq!(blue.b(), 255);
    /// ```
    #[inline]
    pub const fn b(&self) -> u8 {
        self.b
    }

    /// Sets the blue channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut blue = colo_rs::Rgba::new(0, 0, 128, 255);
    /// blue.set_b(255);
    /// assert_eq!(blue.b(), 255);
    /// ```
    #[inline]
    pub fn set_b(&mut self, value: u8) {
        self.b = value;
    }

    /// Gets the normalized blue channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let blue = colo_rs::Rgba::from((0.0, 0.0, 1.0, 1.0));
    /// assert_eq!(blue.b_norm(), 1.0);
    /// ```
    #[inline]
    pub fn b_norm(&self) -> f64 {
        Self::normalize(self.b())
    }

    /// Sets the normalized blue channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut blue = colo_rs::Rgba::from((0.0, 0.0, 0.1, 1.0));
    /// blue.set_b_norm(1.0);
    /// assert_eq!(blue.b_norm(), 1.0);
    /// ```
    #[inline]
    pub fn set_b_norm(&mut self, value: f64) {
        self.set_b(Self::denormalize(value));
    }

    /// Gets the alpha channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let black = colo_rs::Rgba::new(0, 0, 0, 255);
    /// assert_eq!(black.a(), 255);
    /// ```
    #[inline]
    pub const fn a(&self) -> u8 {
        self.a
    }

    /// Sets the alpha channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut black = colo_rs::Rgba::new(0, 0, 0, 128);
    /// black.set_a(255);
    /// assert_eq!(black.a(), 255);
    /// ```
    #[inline]
    pub fn set_a(&mut self, value: u8) {
        self.a = value;
    }

    /// Gets the normalized alpha channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let black = colo_rs::Rgba::from((0.0, 0.0, 0.0, 1.0));
    /// assert_eq!(black.a_norm(), 1.0);
    /// ```
    #[inline]
    pub fn a_norm(&self) -> f64 {
        Self::normalize(self.a())
    }

    /// Sets the normalized alpha channel value.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut black = colo_rs::Rgba::from((0.0, 0.0, 0.0, 0.5));
    /// black.set_a_norm(1.0);
    /// assert_eq!(black.a_norm(), 1.0);
    /// ```
    #[inline]
    pub fn set_a_norm(&mut self, value: f64) {
        self.set_a(Self::denormalize(value));
    }

    /// Checks if the color is transparent.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::new(255, 0, 0, 255);
    /// let green = colo_rs::Rgba::new(0, 255, 0, 255);
    /// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
    /// let black = colo_rs::Rgba::new(0, 0, 0, 255);
    /// let white = colo_rs::Rgba::new(255, 255, 255, 255);
    /// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
    /// let transparent = colo_rs::Rgba::default();
    ///
    /// assert!(!red.is_transparent());
    /// assert!(!green.is_transparent());
    /// assert!(!blue.is_transparent());
    /// assert!(!black.is_transparent());
    /// assert!(!white.is_transparent());
    /// assert!(!translucent_gray.is_transparent());
    /// assert!(transparent.is_transparent());
    /// ```
    #[inline]
    pub const fn is_transparent(&self) -> bool {
        self.a() == Self::CHANNEL_MIN
    }

    /// Checks if the color is translucent.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::new(255, 0, 0, 255);
    /// let green = colo_rs::Rgba::new(0, 255, 0, 255);
    /// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
    /// let black = colo_rs::Rgba::new(0, 0, 0, 255);
    /// let white = colo_rs::Rgba::new(255, 255, 255, 255);
    /// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
    /// let transparent = colo_rs::Rgba::default();
    ///
    /// assert!(!red.is_translucent());
    /// assert!(!green.is_translucent());
    /// assert!(!blue.is_translucent());
    /// assert!(!black.is_translucent());
    /// assert!(!white.is_translucent());
    /// assert!(translucent_gray.is_translucent());
    /// assert!(!transparent.is_translucent());
    /// ```
    #[inline]
    pub const fn is_translucent(&self) -> bool {
        self.a() > Self::CHANNEL_MIN && self.a() < Self::CHANNEL_MAX
    }

    /// Checks if the color is opaque.
    ///
    /// # Examples
    ///
    /// ```
    /// let red = colo_rs::Rgba::new(255, 0, 0, 255);
    /// let green = colo_rs::Rgba::new(0, 255, 0, 255);
    /// let blue = colo_rs::Rgba::new(0, 0, 255, 255);
    /// let black = colo_rs::Rgba::new(0, 0, 0, 255);
    /// let white = colo_rs::Rgba::new(255, 255, 255, 255);
    /// let translucent_gray = colo_rs::Rgba::new(128, 128, 128, 128);
    /// let transparent = colo_rs::Rgba::default();
    ///
    /// assert!(red.is_opaque());
    /// assert!(green.is_opaque());
    /// assert!(blue.is_opaque());
    /// assert!(black.is_opaque());
    /// assert!(white.is_opaque());
    /// assert!(!translucent_gray.is_opaque());
    /// assert!(!transparent.is_opaque());
    /// ```
    #[inline]
    pub const fn is_opaque(&self) -> bool {
        self.a() == Self::CHANNEL_MAX
    }

    /// Normalize a channel from the range \[0, 255\] to the range \[0.0, 1.0\].
    #[inline]
    fn normalize(channel: u8) -> f64 {
        channel as f64 / Self::CHANNEL_MAX as f64
    }

    /// Denormalize a channel from the range \[0.0, 1.0\] to the range \[0, 255\].
    #[inline]
    fn denormalize(channel: f64) -> u8 {
        use std::ops::Mul;
        channel
            .clamp(Self::NORM_CHANNEL_MIN, Self::NORM_CHANNEL_MAX)
            .mul(Self::CHANNEL_MAX as f64)
            .round() as u8
    }
}

impl Display for Rgba {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "#{:02X}{:02X}{:02X}{:02X}",
            self.r(),
            self.g(),
            self.b(),
            self.a()
        )
    }
}

impl From<(u8, u8, u8, u8)> for Rgba {
    #[inline]
    fn from((r, g, b, a): (u8, u8, u8, u8)) -> Self {
        Self::new(r, g, b, a)
    }
}

impl From<Rgba> for (u8, u8, u8, u8) {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        (rgba.r(), rgba.g(), rgba.b(), rgba.a())
    }
}

impl From<(u8, u8, u8)> for Rgba {
    #[inline]
    fn from((r, g, b): (u8, u8, u8)) -> Self {
        Self::new(r, g, b, Self::CHANNEL_MAX)
    }
}

impl From<Rgba> for (u8, u8, u8) {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        (rgba.r(), rgba.g(), rgba.b())
    }
}

impl From<[u8; 4]> for Rgba {
    #[inline]
    fn from([r, g, b, a]: [u8; 4]) -> Self {
        Self::new(r, g, b, a)
    }
}

impl From<Rgba> for [u8; 4] {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        [rgba.r(), rgba.g(), rgba.b(), rgba.a()]
    }
}

impl From<[u8; 3]> for Rgba {
    #[inline]
    fn from([r, g, b]: [u8; 3]) -> Self {
        Self::new(r, g, b, Self::CHANNEL_MAX)
    }
}

impl From<Rgba> for [u8; 3] {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        [rgba.r(), rgba.g(), rgba.b()]
    }
}

impl From<u32> for Rgba {
    #[inline]
    fn from(hex: u32) -> Self {
        Self::from(hex.to_be_bytes())
    }
}

impl From<Rgba> for u32 {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        u32::from_be_bytes(rgba.into())
    }
}

impl From<(f64, f64, f64, f64)> for Rgba {
    #[inline]
    fn from((r, g, b, a): (f64, f64, f64, f64)) -> Self {
        Self::new(
            Self::denormalize(r),
            Self::denormalize(g),
            Self::denormalize(b),
            Self::denormalize(a),
        )
    }
}

impl From<Rgba> for (f64, f64, f64, f64) {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        (rgba.r_norm(), rgba.g_norm(), rgba.b_norm(), rgba.a_norm())
    }
}

impl From<(f64, f64, f64)> for Rgba {
    #[inline]
    fn from((r, g, b): (f64, f64, f64)) -> Self {
        Self::new(
            Self::denormalize(r),
            Self::denormalize(g),
            Self::denormalize(b),
            Self::CHANNEL_MAX,
        )
    }
}

impl From<Rgba> for (f64, f64, f64) {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        (rgba.r_norm(), rgba.g_norm(), rgba.b_norm())
    }
}

impl From<[f64; 4]> for Rgba {
    #[inline]
    fn from([r, g, b, a]: [f64; 4]) -> Self {
        Self::from((r, g, b, a))
    }
}

impl From<Rgba> for [f64; 4] {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        [rgba.r_norm(), rgba.g_norm(), rgba.b_norm(), rgba.a_norm()]
    }
}

impl From<[f64; 3]> for Rgba {
    #[inline]
    fn from([r, g, b]: [f64; 3]) -> Self {
        Self::from((r, g, b))
    }
}

impl From<Rgba> for [f64; 3] {
    #[inline]
    fn from(rgba: Rgba) -> Self {
        [rgba.r_norm(), rgba.g_norm(), rgba.b_norm()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rgba_new() {
        let transparent = Rgba::default();

        let white = Rgba::new(255, 255, 255, 255);
        let transparent_black = Rgba::new(0, 0, 0, 0);

        assert_ne!(white, transparent);
        assert_eq!(transparent_black, transparent);
    }

    #[test]
    fn test_rgba_is_transparent() {
        let transparent = Rgba::default();
        let translucent_gray = Rgba::new(128, 128, 128, 128);
        let white = Rgba::new(255, 255, 255, 255);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }

    #[test]
    fn test_rgba_is_translucent() {
        let transparent = Rgba::default();
        let translucent_gray = Rgba::new(128, 128, 128, 128);
        let white = Rgba::new(255, 255, 255, 255);

        assert!(!transparent.is_translucent());
        assert!(translucent_gray.is_translucent());
        assert!(!white.is_translucent());
    }

    #[test]
    fn test_rgba_is_opaque() {
        let transparent = Rgba::default();
        let translucent_gray = Rgba::new(128, 128, 128, 128);
        let white = Rgba::new(255, 255, 255, 255);

        assert!(transparent.is_transparent());
        assert!(!translucent_gray.is_transparent());
        assert!(!white.is_transparent());
    }
}
