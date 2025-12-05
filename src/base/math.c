#include "math.h"

// =============================================================================
// Scalars:
// =============================================================================
F32 lerp_f32 (F32 a, F32 b, F32 t) { return a + (b - a)*clamp(t, 0, 1.0); }

// =============================================================================
// Vectors:
// =============================================================================
Vec3 add_v3       (Vec3 a, Vec3 b)        { return vec3(a.x+b.x, a.y+b.y, a.z+b.z); }
Vec3 sub_v3       (Vec3 a, Vec3 b)        { return vec3(a.x-b.x, a.y-b.y, a.z-b.z); }
F32  dot_v3       (Vec3 a, Vec3 b)        { return a.x*b.x + a.y*b.y + a.z*b.z; }
Vec3 cross        (Vec3 a, Vec3 b)        { return vec3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x); }
Vec3 normcross    (Vec3 a, Vec3 b)        { return normalize(cross(a, b)); }
Vec3 mul_f32_v3   (F32 s, Vec3 v)         { return vec3(v.x*s, v.y*s, v.z*s); }
Vec3 mul_v3_v3    (Vec3 a, Vec3 b)        { return vec3(a.x*b.x, a.y*b.y, a.z*b.z); }
F32  len_v3       (Vec3 v)                { return sqrt(v.x*v.x + v.y*v.y + v.z*v.z); }
Vec3 normalize_v3 (Vec3 v)                { return mul(1.f/len(v), v); }
Vec3 lerp_v3      (Vec3 a, Vec3 b, F32 t) { return vec3(lerp_f32(a.x, b.x, t), lerp_f32(a.y, b.y, t), lerp_f32(a.z, b.z, t)); }
Void print_v3     (Vec3 v, AString *a, CString p, CString s) { astr_push_fmt(a, "%s(x=%f, y=%f, z=%f)%s", p, v.x, v.y, v.z, s); }

// =============================================================================
// Matrices:
// =============================================================================
Mat4 mat4          (F32 d)   { return (Mat4){ .v[0][0]=d,   .v[1][1]=d,   .v[2][2]=d,   .v[3][3]=d }; }
Mat4 mat_scale     (Vec3 v)  { return (Mat4){ .v[0][0]=v.x, .v[1][1]=v.y, .v[2][2]=v.z, .v[3][3]=1.0 }; }
Mat4 mat_uscale    (F32 s)   { return (Mat4){ .v[0][0]=s,   .v[1][1]=s,   .v[2][2]=s,   .v[3][3]=1.0 }; }
Mat4 mat_translate (Vec3 dt) { Mat4 r = mat4(1.f); r.v[3][0] = dt.x; r.v[3][1] = dt.y; r.v[3][2] = dt.z; return r; }

Void print_m4 (Mat4 m, AString *astr, CString prefix, CString suffix) {
    astr_push_fmt(
        astr,
        "%s"
        "|%+f, %+f, %+f %+f|\n"
        "|%+f, %+f, %+f %+f|\n"
        "|%+f, %+f, %+f %+f|\n"
        "|%+f, %+f, %+f %+f|\n"
        "%s",
        prefix,
        m.v[0][0], m.v[1][0], m.v[2][0], m.v[3][0],
        m.v[0][1], m.v[1][1], m.v[2][1], m.v[3][1],
        m.v[0][2], m.v[1][2], m.v[2][2], m.v[3][2],
        m.v[0][3], m.v[1][3], m.v[2][3], m.v[3][3],
        suffix
    );
}

Mat4 mat_rotate (Rad angle, Vec3 axis) {
    axis = normalize(axis);
    F32 sin_theta = sin(angle);
    F32 cos_theta = cos(angle);
    F32 cos_value = 1.f - cos_theta;
    Mat4 r    = mat4(1.f);
    r.v[0][0] = (axis.x * axis.x * cos_value) + cos_theta;
    r.v[0][1] = (axis.x * axis.y * cos_value) + (axis.z * sin_theta);
    r.v[0][2] = (axis.x * axis.z * cos_value) - (axis.y * sin_theta);
    r.v[1][0] = (axis.y * axis.x * cos_value) - (axis.z * sin_theta);
    r.v[1][1] = (axis.y * axis.y * cos_value) + cos_theta;
    r.v[1][2] = (axis.y * axis.z * cos_value) + (axis.x * sin_theta);
    r.v[2][0] = (axis.z * axis.x * cos_value) + (axis.y * sin_theta);
    r.v[2][1] = (axis.z * axis.y * cos_value) - (axis.x * sin_theta);
    r.v[2][2] = (axis.z * axis.z * cos_value) + cos_theta;
    return r;
}

// OpenGl clip volume.
Mat4 mat_ortho (F32 left, F32 right, F32 bottom, F32 top, F32 near, F32 far) {
    Mat4 r    = {};
    r.v[0][0] = 2.f / (right - left);
    r.v[1][1] = 2.f / (top - bottom);
    r.v[2][2] = -2.f / (far - near);
    r.v[3][0] = (right + left) / (left - right);
    r.v[3][1] = (top + bottom) / (bottom - top);
    r.v[3][2] = (far + near) / (near - far);
    r.v[3][3] = 1.f;
    return r;
}

// OpenGl clip volume.
Mat4 mat_perspective (Rad fovy, F32 aspect, F32 near, F32 far) {
    F32 tf2   = tan(fovy / 2.f);
    Mat4 r    = {};
    r.v[0][0] = 1.f / (aspect * tf2);
    r.v[1][1] = 1.f / tf2;
    r.v[2][2] = (far + near) / (near - far);
    r.v[2][3] = -1.f;
    r.v[3][2] = (2.f * far * near) / (near - far);
    return r;
}

Mat4 mat_look_at (Vec3 pos, Vec3 target, Vec3 up) {
    Vec3 f = normalize(sub(target, pos));
    Vec3 s = normcross(f, up);
    Vec3 u = cross(s, f);
    Mat4 r;
    r.v[0][0] = s.x;
    r.v[1][0] = s.y;
    r.v[2][0] = s.z;
    r.v[0][1] = u.x;
    r.v[1][1] = u.y;
    r.v[2][1] = u.z;
    r.v[0][2] = -f.x;
    r.v[1][2] = -f.y;
    r.v[2][2] = -f.z;
    r.v[0][3] = 0;
    r.v[1][3] = 0;
    r.v[2][3] = 0;
    r.v[3][0] = -dot(s, pos);
    r.v[3][1] = -dot(u, pos);
    r.v[3][2] = dot(f, pos);
    r.v[3][3] = 1.0f;
    return r;
}

Mat4 mul_m4 (Mat4 a, Mat4 b) {
    Mat4 r;
    for (U64 j = 0; j < 4; j += 1) {
        for (U64 i = 0; i < 4; i += 1) {
            r.v[i][j] = (a.v[0][j] * b.v[i][0]) +
                        (a.v[1][j] * b.v[i][1]) +
                        (a.v[2][j] * b.v[i][2]) +
                        (a.v[3][j] * b.v[i][3]);
        }
    }
    return r;
}
